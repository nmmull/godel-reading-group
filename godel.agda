open import Data.Product using (Σ; _,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product.Properties using (≡-dec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties renaming (_≟_ to ≡-dec-ℕ)
open import Data.List using (List; _∷_; []; _++_)
open import Relation.Nullary.Decidable using (yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app)


Variable : Set
Variable = ℕ × ℕ

_≟_ : DecidableEquality Variable
_≟_ = ≡-dec ≡-dec-ℕ ≡-dec-ℕ

level : Variable → ℕ
level (_ , v) = v

ident : Variable → ℕ
ident (i , _) = i

data PrimSign : Set where
  ~̂ : PrimSign
  ∨̂ : PrimSign
  Π̂ : PrimSign
  0̂ : PrimSign
  𝑓̂ : PrimSign
  ⦅̂ : PrimSign
  ⦆̂ : PrimSign
  ⟨_⟩̂ : Variable -> PrimSign

SignComb : Set
SignComb = List PrimSign

infix 40 𝑓_
data Sign : ℕ → Set where
  ⟨_⟩ : (v : Variable) → Sign (level v)
  0̇ : Sign 0
  𝑓_ : Sign 0 → Sign 0

sign→comb : ∀{n} → Sign n → SignComb
sign→comb ⟨ i ⟩ = ⟨ i ⟩̂ ∷ []
sign→comb 0̇ = 0̂ ∷ []
sign→comb (𝑓 s) = 𝑓̂ ∷ sign→comb s

infix 35 _⦅_⦆
infix 25 ~_
infix 33 ⟨_⟩Π_
infix 24 _∨_
data Formula : Set where
  _⦅_⦆ : ∀{n} → Sign (1 + n) → Sign n → Formula
  ~_ : Formula → Formula
  _∨_ : Formula → Formula → Formula
  ⟨_⟩Π_ : Variable → Formula → Formula

subst-sign : ∀{n} → Sign n → (v : Variable) → Sign (level v) → Sign n
subst-sign ⟨ x ⟩ v b with x ≟ v
...                    | yes refl = b
...                    | _        = ⟨ x ⟩
subst-sign 0̇ v b = 0̇
subst-sign (𝑓 a) v b = 𝑓 (subst-sign a v b)

subst : Formula → (v : Variable) → Sign (level v) → Formula
subst (a ⦅ c ⦆) v b = subst-sign a v b ⦅ subst-sign c v b ⦆
subst (~ a) v b = ~ (subst a v b)
subst (a ∨ c) v b = (subst a v b) ∨ (subst c v b)
subst (⟨ x ⟩Π a) v b with x ≟ v
...                    | yes _ = ⟨ x ⟩Π (subst a v b)
...                    | _     = ⟨ x ⟩Π a

form→comb : Formula → SignComb
form→comb (a ⦅ b ⦆) = sign→comb a ++ ⦅̂ ∷ sign→comb b ++ ⦆̂ ∷ []
form→comb (~ a) = ~̂ ∷ ⦅̂ ∷ form→comb a ++ ⦆̂ ∷ []
form→comb (a ∨ b) = ⦅̂ ∷ form→comb a ++ ⦆̂ ∷ ∨̂ ∷ ⦅̂ ∷ form→comb b ++ ⦆̂ ∷ []
form→comb (⟨ x ⟩Π a) = ⟨ x ⟩̂ ∷ Π̂ ∷ ⦅̂ ∷ form→comb a ++ ⦆̂ ∷ []

infix 32 _∙_
_∙_ : Formula → Formula → Formula
p ∙ q = ~ p ∨ ~ q

infixr 23 _⊃_
_⊃_ : Formula → Formula → Formula
p ⊃ q = (~ p) ∨ q

x : ℕ
x = 0

y : ℕ
y = 1

infix 35 _＝_
_＝_ : ∀{n} → Sign n → Sign n → Formula
_＝_ {n} s₁ s₂ = ⟨ x , 1 + n ⟩Π (⟨ x , 1 + n ⟩ ⦅ s₁ ⦆ ⊃ ⟨ x , 1 + n ⟩ ⦅ s₂ ⦆)

axiom_I1 : Formula
axiom_I1 = ~ (𝑓 ⟨ x , 0 ⟩ ＝ 0̇)

axiom_I2 : Formula
axiom_I2 = 𝑓 ⟨ x , 0 ⟩ ＝ 𝑓 ⟨ y , 0 ⟩ ⊃ ⟨ x , 0 ⟩ ＝ ⟨ y , 0 ⟩

axiom_I3 : Formula
axiom_I3 = ⟨ x , 1 ⟩ ⦅ 0̇ ⦆ ∙ ⟨ x , 0 ⟩Π (⟨ x , 1 ⟩ ⦅ ⟨ x , 0 ⟩ ⦆ ⊃ ⟨ x , 1 ⟩ ⦅ 𝑓 ⟨ x , 0 ⟩ ⦆) ⊃ ⟨ x , 0 ⟩Π (⟨ x , 1 ⟩ ⦅ ⟨ x , 0 ⟩ ⦆)

axiom_II1 : Formula → Formula
axiom_II1 p = p ∨ p ⊃ p

axiom_II2 : Formula → Formula → Formula
axiom_II2 p q = p ⊃ p ∨ q

axiom_II3 : Formula → Formula → Formula
axiom_II3 p q = p ∨ q ⊃ q ∨ p

axiom_II4 : Formula → Formula → Formula → Formula
axiom_II4 p q r = (p ⊃ q) ⊃ (r ∨ p ⊃ r ∨ q)
