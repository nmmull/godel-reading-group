open import Data.Product using (Σ; _,_; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat using (ℕ; zero; suc;  _+_; _*_; _^_)
open import Data.Nat.Properties renaming (_≟_ to ≡-dec-ℕ)
open import Data.List using (List; _∷_; []; _++_; map)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app)
open import Relation.Nullary using (¬_)

Var : Set
Var = ℕ × ℕ

_≟_ : DecidableEquality Var
_≟_ = ≡-dec ≡-dec-ℕ ≡-dec-ℕ

level : Var → ℕ
level (_ , v) = v

ident : Var → ℕ
ident (i , _) = i

x = 0
y = 1
z = 2

x₀̌ : Var
x₀̌ = x , 0

y₀̌ : Var
y₀̌ = y , 0

z₀̌ : Var
z₀̌ = z , 0

x₁̌ : Var
x₁̌ = x , 1

y₁̌ : Var
y₁̌ = y , 1

z₁̌ : Var
z₁̌ = z , 1

x₂̌ : Var
x₂̌ = x , 2

y₂̌ : Var
y₂̌ = y , 2

z₂̌ : Var
z₂̌ = z , 2

data PrimSign : Set where
  ~̂ : PrimSign
  ∨̂ : PrimSign
  Π̂ : PrimSign
  0̂ : PrimSign
  𝑓̂ : PrimSign
  ⦅̂ : PrimSign
  ⦆̂ : PrimSign
  ⟨_⟩̂ : Var -> PrimSign

SignComb : Set
SignComb = List PrimSign

infix 90 𝑓_
data Sign : ℕ → Set where
  ⟨_⟩ : (v : Var) → Sign (level v)
  0̇ : Sign 0
  𝑓_ : Sign 0 → Sign 0

x₀ = ⟨ x₀̌ ⟩
y₀ = ⟨ y₀̌ ⟩
z₀ = ⟨ z₀̌ ⟩
x₁ = ⟨ x₁̌ ⟩
y₁ = ⟨ y₁̌ ⟩
z₁ = ⟨ z₁̌ ⟩
x₂ = ⟨ x₂̌ ⟩
y₂ = ⟨ y₂̌ ⟩
z₂ = ⟨ z₂̌ ⟩

sign→comb : ∀{n} → Sign n → SignComb
sign→comb ⟨ i ⟩ = ⟨ i ⟩̂ ∷ []
sign→comb 0̇ = 0̂ ∷ []
sign→comb (𝑓 s) = 𝑓̂ ∷ sign→comb s

data FreeS : ∀{n} → (v : Var) → Sign n → Set where
  var-free : ∀{v} → FreeS v ⟨ v ⟩
  𝑓-free : ∀{v s} → FreeS v s → FreeS v (𝑓 s)

free-s? : ∀{n} (v : Var) (s : Sign n) → Dec (FreeS v s)
free-s? v ⟨ w ⟩ with v ≟ w
...                  | yes refl = yes var-free
...                  | no v≢w = no λ free → v≢w (implies-≡ free) where
  implies-≡ : ∀ {v w} →  FreeS v ⟨ w ⟩ → v ≡ w
  implies-≡ var-free = refl
free-s? _ 0̇ = no λ ()
free-s? v (𝑓 s) with free-s? v s
...                   | yes prf = yes (𝑓-free prf)
...                   | no ¬free = no (λ free → ¬free (free-𝑓 free)) where
  free-𝑓 : ∀{v s} → FreeS v (𝑓 s) → FreeS v s
  free-𝑓 (𝑓-free free) = free

infix 80 _⦅_⦆
infix 50 ~_
infix 40 _∨_
infix 70 ⟨_⟩Π_
data Form : Set where
  _⦅_⦆ : ∀{n} → Sign (1 + n) → Sign n → Form
  ~_ : Form → Form
  _∨_ : Form → Form → Form
  ⟨_⟩Π_ : Var → Form → Form

form→comb : Form → SignComb
form→comb (a ⦅ b ⦆) = sign→comb a ++ ⦅̂ ∷ sign→comb b ++ ⦆̂ ∷ []
form→comb (~ a) = ~̂ ∷ ⦅̂ ∷ form→comb a ++ ⦆̂ ∷ []
form→comb (a ∨ b) = ⦅̂ ∷ form→comb a ++ ⦆̂ ∷ ∨̂ ∷ ⦅̂ ∷ form→comb b ++ ⦆̂ ∷ []
form→comb (⟨ x ⟩Π a) = ⟨ x ⟩̂ ∷ Π̂ ∷ ⦅̂ ∷ form→comb a ++ ⦆̂ ∷ []

subst-s : ∀{n} → Sign n → (v : Var) → Sign (level v) → Sign n
subst-s ⟨ x ⟩ v b with x ≟ v
...                    | yes refl = b
...                    | _        = ⟨ x ⟩
subst-s 0̇ v b = 0̇
subst-s (𝑓 a) v b = 𝑓 (subst-s a v b)

subst : Form → (v : Var) → Sign (level v) → Form
subst (a ⦅ c ⦆) v b = subst-s a v b ⦅ subst-s c v b ⦆
subst (~ a) v b = ~ (subst a v b)
subst (a ∨ c) v b = (subst a v b) ∨ (subst c v b)
subst (⟨ x ⟩Π a) v b with x ≟ v
...                    | yes _ = ⟨ x ⟩Π a
...                    | _     = ⟨ x ⟩Π (subst a v b)

data Free : Var → Form → Set where
  app-free-l : ∀{n v} {s₁ : Sign (1 + n)} {s₂ : Sign n} → FreeS v s₁ → Free v (s₁ ⦅ s₂ ⦆)
  app-free-r : ∀{n v} {s₁ : Sign (1 + n)} {s₂ : Sign n} → FreeS v s₂ → Free v (s₁ ⦅ s₂ ⦆)
  ~-free : ∀{v p} → Free v p → Free v (~ p)
  ∨-free-l : ∀{v p q} → Free v p → Free v (p ∨ q)
  ∨-free-r : ∀{v p q} → Free v q → Free v (p ∨ q)
  Π-free : ∀{v w p} → v ≢ w → Free v p → Free v (⟨ w ⟩Π p)

free? : (v : Var) → (p : Form) → Dec (Free v p)
free? v (s₁ ⦅ s₂ ⦆) with free-s? v s₁ | free-s? v s₂
free? v (s₁ ⦅ s₂ ⦆)    | yes free        | _           = yes (app-free-l free)
free? v (s₁ ⦅ s₂ ⦆)    | no _            | yes free    = yes (app-free-r free)
free? v (s₁ ⦅ s₂ ⦆)    | no ¬free-s₁     | no ¬free-s₂ = no λ free → [ ¬free-s₁ , ¬free-s₂ ] (free-app free) where
  free-app : ∀{n v} {s₁ : Sign (1 + n)} {s₂ : Sign n} → Free v (s₁ ⦅ s₂ ⦆) → FreeS v s₁ ⊎ FreeS v s₂
  free-app (app-free-l free) = inj₁ free
  free-app (app-free-r free) = inj₂ free
free? v (~ p) with free? v p
...                 | yes free = yes (~-free free)
...                 | no ¬free = no (λ free → ¬free (free-~ free)) where
  free-~ : ∀{v p} → Free v (~ p) → Free v p
  free-~ (~-free free) = free
free? v (p ∨ q) with free? v p | free? v q
free? v (p ∨ q)    | yes free     | _          = yes (∨-free-l free)
free? v (p ∨ q)    | no _         | yes free   = yes (∨-free-r free)
free? v (p ∨ q)    | no ¬free-p   | no ¬free-q = no λ free → [ ¬free-p , ¬free-q ] (free-∨ free) where
  free-∨ : ∀{v p q} → Free v (p ∨ q) → Free v p ⊎ Free v q
  free-∨ (∨-free-l free) = inj₁ free
  free-∨ (∨-free-r free) = inj₂ free
free? v (⟨ w ⟩Π p) with v ≟ w   | free? v p
free? v (⟨ w ⟩Π p)    | yes v≡w | _        = no λ free → free-Π₁ free v≡w where
  free-Π₁ : ∀{v w p} → Free v (⟨ w ⟩Π p) → v ≢ w
  free-Π₁ {v} {w} (Π-free v≢w free) = v≢w
free? v (⟨ w ⟩Π p)    | no v≢w  | yes free = yes (Π-free v≢w free)
free? v (⟨ w ⟩Π p)    | no _    | no ¬free = no (λ free → ¬free (free-Π₂ free)) where
  free-Π₂ : ∀{v w p} → Free v (⟨ w ⟩Π p) → Free v p
  free-Π₂ {v} {w} (Π-free x free) = free

data CanSubst : Form → (v : Var) → Sign (level v)  → Set where
  app-subst : ∀{n} {s₁ : Sign (1 + n)} {s₂ : Sign n} {v s} → CanSubst (s₁ ⦅ s₂ ⦆) v s
  ~-subst : ∀ {a v s} → CanSubst a v s → CanSubst (~ a) v s
  ∨-subst : ∀ {a b v s} → CanSubst a v s → CanSubst b v s → CanSubst (a ∨ b) v s
  Π-subst : ∀{x a v s} → ¬ FreeS x s → CanSubst a v s → CanSubst (⟨ x ⟩Π a) v s

-- unicode shortcut: \.
infix 60 _∙_
_∙_ : Form → Form → Form
p ∙ q = ~ (~ p ∨ ~ q)

infixr 30 _⊃_
_⊃_ : Form → Form → Form
p ⊃ q = ~ p ∨ q

infix 80 _＝_
_＝_ : ∀{n} → Sign n → Sign n → Form
_＝_ {n} s₁ s₂ = ⟨ x , 1 + n ⟩Π (⟨ x , 1 + n ⟩ ⦅ s₁ ⦆ ⊃ ⟨ x , 1 + n ⟩ ⦅ s₂ ⦆)

infix 70 ⦅E_⦆_
⦅E_⦆_ : Var → Form → Form
⦅E v ⦆ a = ~ ⟨ v ⟩Π (~ a)

infix 70 _≡̇_
_≡̇_ : Form → Form → Form
p ≡̇ q = p ⊃ q ∙ q ⊃ p

axiom-I1 : Form
axiom-I1 = ~ (𝑓 x₀ ＝ 0̇)

axiom-I2 : Form
axiom-I2 = 𝑓 x₀ ＝ 𝑓 y₀ ⊃ x₀ ＝ y₀

axiom-I3 : Form
axiom-I3 =
  ⟨ x₁̌ ⟩ ⦅ 0̇ ⦆ ∙
  ⟨ x₀̌ ⟩Π (x₁ ⦅ x₀ ⦆ ⊃ x₁ ⦅ 𝑓 x₀ ⦆) ⊃
  ⟨ x₀̌ ⟩Π (x₁ ⦅ x₀ ⦆)

axiom-II1 : Form → Form
axiom-II1 p = p ∨ p ⊃ p

axiom-II2 : Form → Form → Form
axiom-II2 p q = p ⊃ p ∨ q

axiom-II3 : Form → Form → Form
axiom-II3 p q = p ∨ q ⊃ q ∨ p

axiom-II4 : Form → Form → Form → Form
axiom-II4 p q r = (p ⊃ q) ⊃ (r ∨ p ⊃ r ∨ q)

-- substitutability is folded into provability
axiom-III1 : Form → (v : Var) → Sign (level v) → Form
axiom-III1 a v s = ⟨ v ⟩Π a ⊃ subst a v s

-- not-free is folded into provability
axiom-III2 : (a b : Form) → (v : Var) → Form
axiom-III2 a b v = ⟨ v ⟩Π (b ∨ a) ⊃ b ∨ ⟨ v ⟩Π a

-- not-free is folded into provability
axiom-IV : (u v : Var) → (a : Form) → 1 + level v ≡ level u → Form
axiom-IV u v a 1+v≡u = ⦅E u ⦆ (⟨ v ⟩Π (u-s ⦅ v-s ⦆ ≡̇ a)) where
  v-s : Sign (level v)
  v-s = ⟨ v ⟩

  u-s : Sign (1 + level v)
  u-s rewrite 1+v≡u = ⟨ u ⟩

axiom-V : (n : ℕ) → Form
axiom-V n =
  ⟨ x , n ⟩Π (⟨ x , 1 + n ⟩ ⦅ ⟨ x , n ⟩ ⦆ ≡̇ ⟨ y , 1 + n ⟩ ⦅ ⟨ x , n ⟩ ⦆) ⊃
  ⟨ x , 1 + n ⟩ ＝ ⟨ y , 1 + n ⟩

data Provable (C : Form → Set) : Form → Set where
  prove-in-C : ∀{a} → C a → Provable C a
  prove-axiom-I1 : Provable C axiom-I1
  prove-axiom-I2 : Provable C axiom-I2
  prove-axiom-I3 : Provable C axiom-I3
  prove-axiom-II1 : ∀{p} → Provable C (axiom-II1 p)
  prove-axiom-II2 : ∀{p q} → Provable C (axiom-II2 p q)
  prove-axiom-II3 : ∀{p q} → Provable C (axiom-II3 p q)
  prove-axiom-II4 : ∀{p q r} → Provable C (axiom-II4 p q r)
  prove-axiom-III1 : ∀{a v s} → CanSubst a v s → Provable C (axiom-III1 a v s)
  prove-axiom-III2 : ∀{a b v} → ¬ Free v b → Provable C (axiom-III2 a b v)
  prove-axiom-IV :
    ∀{u v a} →
    ¬ Free u a →
    (prf : 1 + level v ≡ level u) →
    Provable C (axiom-IV u v a prf)
  prove-axiom-V : ∀{n} → Provable C (axiom-V n)
  modus-ponens : ∀{b c} → Provable C (b ⊃ c) → Provable C b → Provable C c
  generalize : ∀{v a} → Provable C a → Provable C (⟨ v ⟩Π a)

variable
  C : Form → Set
  p q r : Form

prove-⊃-trans : Provable C ((q ⊃ r) ⊃ (p ⊃ q) ⊃ (p ⊃ r))
prove-⊃-trans = prove-axiom-II4

⊃-trans₁ :
  Provable C (q ⊃ r) →
  Provable C ((p ⊃ q) ⊃ p ⊃ r)
⊃-trans₁ = modus-ponens prove-⊃-trans

⊃-trans₂ :
  Provable C (q ⊃ r) →
  Provable C (p ⊃ q) →
  Provable C (p ⊃ r)
⊃-trans₂ q⊃r = modus-ponens (⊃-trans₁ q⊃r)

infixr 100 _⟫_
_⟫_ :
  Provable C (p ⊃ q) →
  Provable C (q ⊃ r) →
  Provable C (p ⊃ r)
p⊃q ⟫ q⊃r = ⊃-trans₂ q⊃r p⊃q

prove-⊃-refl : Provable C (p ⊃ p)
prove-⊃-refl =
  -- p ⊃ p ∨ p
  -- p ∨ p ⊃ p
  prove-axiom-II2 ⟫
  prove-axiom-II1

⊃-refl = prove-⊃-refl

prove-∨-contraction : Provable C (p ∨ p ⊃ p)
prove-∨-contraction = prove-axiom-II1

∨-contraction : Provable C (p ∨ p) → Provable C p
∨-contraction = modus-ponens prove-∨-contraction

prove-∨-sym : Provable C (p ∨ q ⊃ q ∨ p)
prove-∨-sym = prove-axiom-II3

∨-sym : Provable C (p ∨ q) → Provable C (q ∨ p)
∨-sym = modus-ponens prove-∨-sym

prove-lem : ∀{C p} → Provable C (p ∨ ~ p)
prove-lem = ∨-sym ⊃-refl

lem = prove-lem

prove-∨-intro-l : Provable C (p ⊃ p ∨ q)
prove-∨-intro-l = prove-axiom-II2

∨-intro-l : Provable C p → Provable C (p ∨ q)
∨-intro-l = modus-ponens prove-∨-intro-l

prove-∨-intro-r : Provable C (q ⊃ p ∨ q)
prove-∨-intro-r =
  -- q ⊃ q ∨ p
  -- q ∨ p ⊃ p ∨ q
  prove-∨-intro-l ⟫
  prove-∨-sym

∨-intro-r : Provable C q → Provable C (p ∨ q)
∨-intro-r = modus-ponens prove-∨-intro-r

∨-reflect : ∀{C p q} → Provable C p ⊎ Provable C q → Provable C (p ∨ q)
∨-reflect (inj₁ prove-p) = modus-ponens prove-axiom-II2 prove-p
∨-reflect (inj₂ prove-q) = modus-ponens (prove-axiom-II2 ⟫ prove-axiom-II3) prove-q

prove-∨-⊃-intro : Provable C ((p ⊃ q) ⊃ (r ∨ p ⊃ r ∨ q))
prove-∨-⊃-intro = prove-axiom-II4

∨-⊃-intro₁ : Provable C (p ⊃ q) → Provable C (r ∨ p ⊃ r ∨ q)
∨-⊃-intro₁ = modus-ponens prove-∨-⊃-intro

∨-⊃-intro₂ : Provable C (p ⊃ q) → Provable C (r ∨ p) → Provable C (r ∨ q)
∨-⊃-intro₂ p⊃q = modus-ponens (∨-⊃-intro₁ p⊃q)

prove-∨-⊃-intro-trivial : Provable C ((p ⊃ q) ⊃ (q ∨ p ⊃ q))
prove-∨-⊃-intro-trivial =
  prove-axiom-II4 ⟫
  (⊃-trans₁ prove-∨-contraction)

∨-⊃-intro-trivial₁ : Provable C (p ⊃ q) → Provable C (q ∨ p ⊃ q)
∨-⊃-intro-trivial₁ = modus-ponens prove-∨-⊃-intro-trivial

∨-antecedent₁ :
  Provable C (p ⊃ r) →
  Provable C ((q ⊃ r) ⊃ p ∨ q ⊃ r)
∨-antecedent₁ p⊃r =
  -- (q ⊃ r) ⊃ p ∨ q ⊃ p ∨ r
  -- (p ∨ q ⊃ p ∨ r) ⊃ (p ∨ q ⊃ r)
  prove-∨-⊃-intro ⟫
  (⊃-trans₁ (prove-∨-sym ⟫ (∨-⊃-intro-trivial₁ p⊃r)))

∨-antecedent₂ :
  Provable C (p ⊃ r) →
  Provable C (q ⊃ r) →
  Provable C (p ∨ q ⊃ r)
∨-antecedent₂ p⊃r = modus-ponens (∨-antecedent₁ p⊃r)

prove-∨-assoc-r : Provable C ((p ∨ q) ∨ r ⊃ p ∨ (q ∨ r))
prove-∨-assoc-r =
  ∨-antecedent₂
    (∨-antecedent₂
      prove-∨-intro-l
      (prove-∨-intro-l ⟫ prove-∨-intro-r))
    (prove-∨-intro-r ⟫ prove-∨-intro-r)

∨-assoc-r : Provable C ((p ∨ q) ∨ r) → Provable C (p ∨ (q ∨ r))
∨-assoc-r = modus-ponens prove-∨-assoc-r

prove-∨-assoc-l : Provable C (p ∨ (q ∨ r) ⊃ (p ∨ q) ∨ r)
prove-∨-assoc-l =
  ∨-antecedent₂
    (prove-∨-intro-l ⟫ prove-∨-intro-l)
    (∨-antecedent₂ (prove-∨-intro-r ⟫ prove-∨-intro-l) prove-∨-intro-r)

∨-assoc-l : Provable C (p ∨ (q ∨ r)) → Provable C ((p ∨ q) ∨ r)
∨-assoc-l = modus-ponens prove-∨-assoc-l

prove-∙-intro : Provable C (p ⊃ q ⊃ p ∙ q)
prove-∙-intro =
  -- (~ p ∨ ~ q) ∨ ~ (~ p ∨ ~ q)
  -- ~ p ∨ (~ q ∨ (~ (~ p ∨ ~ q)
  ∨-assoc-r lem

∙-intro₁ : Provable C p → Provable C (q ⊃ p ∙ q)
∙-intro₁ = modus-ponens prove-∙-intro

∙-intro₂ : Provable C p → Provable C q → Provable C (p ∙ q)
∙-intro₂ p = modus-ponens (∙-intro₁ p)

prove-~~-intro : ∀{C p} → Provable C (p ⊃ ~ ~ p)
prove-~~-intro = lem

~~-intro : ∀{C p} → Provable C p → Provable C (~ ~ p)
~~-intro = modus-ponens prove-~~-intro

prove-contrapositive : ∀{C p q} → Provable C ((p ⊃ q) ⊃ ~ q ⊃ ~ p)
prove-contrapositive =
  modus-ponens prove-axiom-II4 prove-~~-intro ⟫
  prove-axiom-II3

contrapositive : ∀{C p q} → Provable C (p ⊃ q) → Provable C (~ q ⊃ ~ p)
contrapositive = modus-ponens prove-contrapositive

prove-∙-sym : Provable C (p ∙ q ⊃ q ∙ p)
prove-∙-sym = contrapositive prove-∨-sym

∙-elim : Provable C (p ∙ q) → Provable C (q ∙ p)
∙-elim = modus-ponens prove-∙-sym

prove-from-trivial : Provable C ((q ∨ ~ q ⊃ p) ⊃ p)
prove-from-trivial = {!!}

prove-~~-elim : Provable C (~ ~ p ⊃ p)
prove-~~-elim =
  -- ~~p ⊃ ~~ p ∨ p
  -- ~~ p ∨ p ⊃ p ∨ ~ p ⊃ p ∨ p
  -- (p ∨ ~ p ⊃ p ∨ p) ⊃ (p ∨ ~p ⊃ p)
  -- (p ∨ ~p ⊃ p) ⊃ p
  prove-∨-intro-l ⟫
  prove-∨-⊃-intro ⟫
  ⊃-trans₁ prove-∨-contraction ⟫
  prove-from-trivial

∙-elim-l : Provable C (p ∙ q ⊃ p)
∙-elim-l = {!!}

＝-refl : ∀{C n} → {s : Sign n} → Provable C (s ＝ s)
＝-refl = generalize ⊃-refl

prime : ℕ → ℕ
prime = {!!} -- this is annoying to implement and will not matter for a while

ϕ-ps : PrimSign → ℕ
ϕ-ps 0̂ = 1
ϕ-ps 𝑓̂ = 3
ϕ-ps ~̂ = 5
ϕ-ps ∨̂ = 7
ϕ-ps Π̂ = 9
ϕ-ps ⦅̂ = 11
ϕ-ps ⦆̂ = 13
ϕ-ps ⟨ x , l ⟩̂ = prime (x + 6) ^ l

ϕ : Form → ℕ
ϕ a = go 0 (form→comb a) where
  go : ℕ → List PrimSign → ℕ
  go n [] = 1
  go n (x ∷ xs) = (prime(n) ^ ϕ-ps x) * go (n + 1) xs

Z : ℕ → Sign 0
Z zero = 0̇
Z (suc n) = 𝑓 (Z n)

equal : Form
equal = x₀ ＝ y₀

subst-Z : ∀{n v s} → subst-s (Z n) v s ≡ Z n
subst-Z {n = zero} = refl
subst-Z {n = suc n} = cong (λ x → 𝑓 x) subst-Z

≡→equal :
  ∀{C m n} →
  m ≡ n →
  Provable C (subst (subst equal x₀̌ (Z m)) y₀̌ (Z n))
≡→equal {m = m} refl rewrite subst-Z {n = m} {v = y₀̌} {s = Z m} = ＝-refl
