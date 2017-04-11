/*
MIT License

Copyright (c) 2017 Simon Schmidt

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

/*
Offers functions to work with Hyper-Complex numbers modulo P.
*/
package hypercomplex

import "math/big"
import "bytes"
import "fmt"
import "io"
import "errors"

/*
Represents a Hyper-Complex number.
The number is represented as an array of integers (*big.Int), where the length
is a power of two. If a MultiComp contains only one element, it represents an
ordinary Number. Otherwise, it consists of two equal-sized halves, where the first
one represents the real part and the second one represents the imaginary part.
*/
type MultiComp []*big.Int

func (m MultiComp) BitLen() int {
	i := 0
	for _,mm := range m {  i+= mm.BitLen() }
	return i
}
func (m MultiComp) String() string {
	sb := bytes.NewBuffer([]byte{'['})
	for i,b := range m {
		if i>0 { sb.WriteByte(',') }
		fmt.Fprintf(sb,"%X",b)
	}
	sb.WriteByte(']')
	return sb.String()
}

func (m MultiComp) Copy() MultiComp {
	n := make(MultiComp,len(m))
	for i,c := range m { n[i]=c }
	return n
}

type Modulus struct{
	Mod *big.Int
}

/*
Creates a MultiComp over the modulus group of the given length 'size'.
The argument 'size' must be a power of two.

This function chooses them deterministically. This function is meant to
be used with SHAKE-128, SHAKE-256 or similar XOF hash functions.
However, the regular "crypto/rand" rand.Reader can be used as well.
*/
func (m Modulus) Deterministic(source io.Reader, size int) (MultiComp,error){
	if (size&(size-1))!=0 { return nil,errors.New("Must be power of two") }
	r := make(MultiComp,size)
	one := big.NewInt(1)
	re := new(big.Int).Sub(m.Mod,one)
	buf := make([]byte,len(re.Bytes()))
	for i := range r {
		_,e := io.ReadFull(source,buf)
		if e!=nil { return nil,e }
		coef := new(big.Int).SetBytes(buf)
		coef.Mod(coef,re)
		coef.Add(coef,one)
		r[i] = coef
	}
	return r,nil
}


func (m Modulus) Add(a,b MultiComp) MultiComp {
	c := make(MultiComp,len(a))
	for i := range c {
		c[i] = new(big.Int).Add(a[i],b[i])
		c[i].Mod(c[i],m.Mod)
	}
	return c
}
func (m Modulus) Sub(a,b MultiComp) MultiComp {
	c := make(MultiComp,len(a))
	for i := range c {
		c[i] = new(big.Int).Sub(a[i],b[i])
		c[i].Mod(c[i],m.Mod)
	}
	return c
}
func (m Modulus) Multiply(a,b MultiComp) MultiComp {
	// assert: len(a)==len(b)
	L := len(a)/2
	if L==0 {
		r := new(big.Int).Mul(a[0],b[0])
		r.Mod(r,m.Mod)
		return MultiComp{r}
	}
	ar := a[:L]
	ai := a[L:]
	
	br := b[:L]
	bi := b[L:]
	/*
	cr = ar*br - ai-bi
	ci = ar*bi + ai*br
	*/
	cr := m.Sub( m.Multiply(ar,br), m.Multiply(ai,bi) )
	ci := m.Add( m.Multiply(ar,bi), m.Multiply(ai,br) )
	return append(cr,ci...)
}
func (m Modulus) Exp(g MultiComp, exp []byte) MultiComp {
	v := make(MultiComp,len(g))
	for i := range v{ v[i] = big.NewInt(0) }
	v[0].SetUint64(1)
	for _,k := range exp {
		for j := 0; j<8; j++ {
			v = m.Multiply(v,v)
			if (k&0x80)==0x80 {
				v = m.Multiply(v,g)
			}
			k <<= 1
		}
	}
	
	return v
}
func (m Modulus) Neg(a MultiComp) MultiComp {
	b := make(MultiComp,len(a))
	for i,aa := range a {
		n := new(big.Int).Neg(aa)
		n.Mod(n,m.Mod)
		b[i] = n
	}
	return b
}
func isZero(a MultiComp) bool {
	zero := big.NewInt(0)
	for _,c := range a {
		if c.Cmp(zero)!=0 { return false }
	}
	return true
}
func zeroes(i int) MultiComp {
	z := make(MultiComp,i)
	for j := range z { z[j] = big.NewInt(0) }
	return z
}

// For a given 'a = (r,i)' it returns '(r,-i mod P)'.
func (m Modulus) Counterpart(a MultiComp) MultiComp{
	L := len(a)/2
	if L==0 { return a }
	ar := a[:L]
	ai := a[L:]
	return append(ar.Copy(),m.Neg(ai)...)
}

// Computes the modulo inverse of a.
func (m Modulus) Inverse(a MultiComp) MultiComp {
	// assert: len(a)==len(b)
	L := len(a)/2
	if L==0 {
		r := new(big.Int).ModInverse(a[0],m.Mod)
		return MultiComp{r}
	}
	ar := a[:L]
	ai := a[L:]
	if isZero(ai) {
		return append(m.Inverse(ar),ai...)
	}
	/*
	Lemma: imaginary(a * counterpart(a)) = 0
	
	Inv(a) = b*Inv(a*b)
	Inv(a) = counterpart(a) * Inv(a*counterpart(a))
	*/
	cp := m.Counterpart(a)
	prod := m.Multiply(a,cp)
	prod = append(m.Inverse(prod[:L]),prod[L:]...)
	
	prod = m.Multiply(prod,cp)
	return prod
}


