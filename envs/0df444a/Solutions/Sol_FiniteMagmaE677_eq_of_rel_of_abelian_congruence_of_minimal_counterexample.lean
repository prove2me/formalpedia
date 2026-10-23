-- Prove2me | solution 1 for FiniteMagmaE677.eq_of_rel_of_abelian_congruence_of_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-23T01:08:44.459681+00:00
-- url     : https://prove2.me/submissions/33315768-e443-4fc2-b56a-40aeb8bd12a0

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# A minimum-order counterexample has no abelian congruence other than equality

Let `op` be a finite `E677` magma that fails `E255` at `z`, such that every `E677` magma on
`Fin n` with `n < |α|` satisfies `E255`, and write `q x = ((x ◇ x) ◇ x) ◇ x`.  Let `r` be an
abelian congruence of `op`: it satisfies the term condition `C(r, r; 0)` (hypothesis
`habel`), where the term operations of arity `k + 1` are the functions
`(Fin (k + 1) → α) → α` in the least set that contains the projections and is closed under
pointwise `op`.  Then `r a b` gives `a = b`.

## Proof

* Suppose `r a b` with `a ≠ b`.  The quotient `Q = α / r` is an `E677` magma
  (`e677_quotOp`) with fewer elements (`card_quotient_lt`), so it satisfies `E255`
  (`e255_of_card_lt`).  At the class of `z` this gives `r (q z) z`.
* Row agreement.  The term condition for the term `y ◇ x`, with `x` the distinguished
  variable, says: if `r t u`, `r s s'` and `s ◇ t = s' ◇ t`, then `s ◇ u = s' ◇ u`.
* Put `s = (z ◇ z) ◇ z`, so `r (s ◇ z) z`.  Right multiplication by `z` maps the class of `s`
  into the class of `z`.  By row agreement and `eq_of_rows_eq_on_class` it is injective; all
  classes have one size (`card_class_eq`), so it is onto, and some element sends `z` to `z`
  (`exists_fixer_of_rowAgreementAt`).  Such an element gives `q z = z`
  (`eq255_from_fixer_exists`), which is false.

The proof uses the term condition only for the term `y ◇ x`.  The helpers are those of the
solutions of Counterexample structure (g) (left cancellation, fixers, classes, the row-agreement
lift) and (k) (quotients, transport to `Fin n`).  Ported from `lean/E677/AbelianLift.lean`,
`lean/E677/MonolithReduction.lean`, `lean/E677/CriticalCore.lean` and
`lean/E677/Spine/Cancellation.lean` of a private repo (Adam McKenna).
-/

universe u
open FiniteMagmaE677

namespace AbelianHelpers

/-! ### Left cancellation and fixers in a finite `E677` magma -/

section Base

variable {α : Type*} [Finite α] {op : α → α → α}

local infixl:70 " ◇ " => op

/-- Left multiplication is injective in a finite `E677` magma. -/
theorem leftMul_inj (h : E677 op) (y : α) : Function.Injective (fun x => y ◇ x) :=
  Finite.injective_iff_surjective.mpr fun x => ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

/-- Left cancellation in a finite `E677` magma. -/
theorem left_cancel (h : E677 op) (y : α) {a b : α} (hab : y ◇ a = y ◇ b) : a = b :=
  leftMul_inj h y hab

/-- The backward recurrence `x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)`. -/
theorem backward_recurrence (h : E677 op) (x y : α) :
    x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) :=
  left_cancel h y (h (y ◇ x) y)

/-- A fixer of `x` is `(x ◇ x) ◇ x`. -/
theorem fixer_unique (h : E677 op) {x y : α} (hfix : y ◇ x = x) : y = (x ◇ x) ◇ x := by
  have hinv : y ◇ (x ◇ (x ◇ y)) = x := by
    have := (h x y).symm
    rwa [hfix] at this
  have hxy : x = x ◇ (x ◇ y) := left_cancel h y (by rw [hfix, hinv])
  exact left_cancel h x (left_cancel h x (hxy.symm.trans (h x x)))

/-- A fixer of `x` gives `E255` at `x`. -/
theorem eq255_from_fixer_exists (h : E677 op) (x : α) (hfix : ∃ y : α, y ◇ x = x) :
    x = ((x ◇ x) ◇ x) ◇ x := by
  obtain ⟨y, hy⟩ := hfix
  rw [← fixer_unique h hy]
  exact hy.symm

/-- Left cancellation modulo a congruence of a finite `E677` magma. -/
theorem rel_of_rel_mul_left (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) {y u v : α}
    (hrel : r (y ◇ u) (y ◇ v)) : r u v := by
  have hr' : r ((y ◇ u) ◇ ((y ◇ (y ◇ u)) ◇ y)) ((y ◇ v) ◇ ((y ◇ (y ◇ v)) ◇ y)) :=
    hcompat _ _ _ _ hrel
      (hcompat _ _ _ _ (hcompat _ _ _ _ (hr.refl y) hrel) (hr.refl y))
  rwa [← backward_recurrence h u y, ← backward_recurrence h v y] at hr'

end Base

/-! ### Classes of a congruence -/

section Classes

variable {α : Type*} [Finite α] {op : α → α → α}

local infixl:70 " ◇ " => op

/-- Left translation by `c` maps the class of `a` injectively into the class of `c ◇ a`. -/
theorem card_class_le_mul_left (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) (c a : α) :
    Nat.card {b : α // r a b} ≤ Nat.card {b : α // r (c ◇ a) b} := by
  refine Nat.card_le_card_of_injective
    (fun b => ⟨c ◇ b.1, hcompat _ _ _ _ (hr.refl c) b.2⟩) ?_
  intro b b' hbb'
  exact Subtype.ext (left_cancel h c (congrArg Subtype.val hbb'))

/-- All classes of a congruence of a finite `E677` magma have the same cardinality.  The
class of `y` injects into the class of `x` through `L_y ∘ L_x ∘ L_(y ◇ x)`. -/
theorem card_class_eq (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) (a b : α) :
    Nat.card {x : α // r a x} = Nat.card {x : α // r b x} := by
  have key : ∀ x y : α, Nat.card {w : α // r y w} ≤ Nat.card {w : α // r x w} := by
    intro x y
    calc Nat.card {w : α // r y w}
        ≤ Nat.card {w : α // r ((y ◇ x) ◇ y) w} := card_class_le_mul_left h hr hcompat _ _
      _ ≤ Nat.card {w : α // r (x ◇ ((y ◇ x) ◇ y)) w} :=
          card_class_le_mul_left h hr hcompat _ _
      _ ≤ Nat.card {w : α // r (y ◇ (x ◇ ((y ◇ x) ◇ y))) w} :=
          card_class_le_mul_left h hr hcompat _ _
      _ = Nat.card {w : α // r x w} := by rw [← h x y]
  exact le_antisymm (key b a) (key a b)

/-- Let `r a a'` and `r (a ◇ b₀) b₀`.  If `a ◇ b = a' ◇ b` for every `b` in the class of
`b₀`, then `a = a'`. -/
theorem eq_of_rows_eq_on_class (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) {a a' b₀ : α}
    (haa' : r a a') (hfix : r (a ◇ b₀) b₀)
    (hrows : ∀ b : α, r b₀ b → a ◇ b = a' ◇ b) : a = a' := by
  have compat : ∀ {a a' b b' : α}, r a a' → r b b' → r (a ◇ b) (a' ◇ b') :=
    fun h1 h2 => hcompat _ _ _ _ h1 h2
  have hc' : a' ◇ b₀ = a ◇ b₀ := (hrows b₀ (hr.refl b₀)).symm
  have hE : a ◇ (b₀ ◇ ((a ◇ b₀) ◇ a)) = b₀ := (h b₀ a).symm
  have hE' : a' ◇ (b₀ ◇ ((a ◇ b₀) ◇ a')) = b₀ := by
    have := (h b₀ a').symm
    rwa [hc'] at this
  -- `b₀ ◇ (b₀ ◇ a)` lies in the class of `b₀`.
  have h1 : r (a ◇ (b₀ ◇ ((a ◇ b₀) ◇ a))) (a ◇ (b₀ ◇ (b₀ ◇ a))) :=
    compat (hr.refl a) (compat (hr.refl b₀) (compat hfix (hr.refl a)))
  rw [hE] at h1
  have h2 : r (b₀ ◇ (b₀ ◇ a)) b₀ :=
    rel_of_rel_mul_left h hr hcompat (hr.trans (hr.symm h1) (hr.symm hfix))
  -- `w = b₀ ◇ ((a ◇ b₀) ◇ a')` lies in the class of `b₀`.
  have hw : r b₀ (b₀ ◇ ((a ◇ b₀) ◇ a')) := by
    have h3 : r (b₀ ◇ ((a ◇ b₀) ◇ a')) (b₀ ◇ (b₀ ◇ a)) :=
      compat (hr.refl b₀) (compat hfix (hr.symm haa'))
    exact hr.symm (hr.trans h3 h2)
  have hagree := hrows _ hw
  rw [hE'] at hagree
  have h4 : b₀ ◇ ((a ◇ b₀) ◇ a') = b₀ ◇ ((a ◇ b₀) ◇ a) :=
    left_cancel h a (hagree.trans hE.symm)
  exact (left_cancel h (a ◇ b₀) (left_cancel h b₀ h4)).symm

/-- Let `r (s ◇ b) b`.  If any two elements of the class of `s` with equal products with
`b` have equal rows on the class of `b`, then some `a` satisfies `a ◇ b = b`.

Right multiplication by `b` maps the class of `s` into the class of `b`; the hypothesis and
`eq_of_rows_eq_on_class` make it injective, and the two classes have the same size, so
some `a` sends `b` to `b`. -/
theorem exists_fixer_of_rowAgreementAt (h : E677 op) {r : α → α → Prop}
    (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) {s b : α}
    (hsb : r (s ◇ b) b)
    (hRA : ∀ a a' : α, r s a → r s a' → a ◇ b = a' ◇ b →
      ∀ u : α, r b u → a ◇ u = a' ◇ u) :
    ∃ a : α, a ◇ b = b := by
  have hmaps : ∀ a : α, r s a → r b (a ◇ b) := fun a ha =>
    hr.symm (hr.trans (hcompat _ _ _ _ (hr.symm ha) (hr.refl b)) hsb)
  let f : {x : α // r s x} → {x : α // r b x} := fun a => ⟨a.1 ◇ b, hmaps a.1 a.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨a', ha'⟩ hf
    have hab : a ◇ b = a' ◇ b := congrArg Subtype.val hf
    have haa' : r a a' := hr.trans (hr.symm ha) ha'
    exact Subtype.ext (eq_of_rows_eq_on_class h hr hcompat haa' (hr.symm (hmaps a ha))
      (hRA a a' ha ha' hab))
  obtain ⟨⟨a, _⟩, hfa⟩ :=
    (hinj.bijective_of_nat_card_le (card_class_eq h hr hcompat b s).le).2 ⟨b, hr.refl b⟩
  exact ⟨a, congrArg Subtype.val hfa⟩

end Classes

/-! ### Quotients by a compatible reflexive, symmetric and transitive relation -/

section Quot

variable {α : Type*} {r : α → α → Prop}

/-- The setoid of a reflexive, symmetric and transitive relation. -/
abbrev setoidOf (hr : Equivalence r) : Setoid α := ⟨r, hr⟩

/-- The operation induced on the quotient by a compatible reflexive, symmetric and transitive
relation. -/
def quotOp (op : α → α → α) (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) :
    Quotient (setoidOf hr) → Quotient (setoidOf hr) → Quotient (setoidOf hr) :=
  Quotient.map₂ op fun _ _ ha _ _ hb => hcompat _ _ _ _ ha hb

/-- `E677` passes to the quotient. -/
theorem e677_quotOp {op : α → α → α} (h : E677 op) (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) :
    E677 (quotOp op hr hcompat) := by
  refine Quotient.ind₂ fun a b => ?_
  exact congrArg (Quotient.mk (setoidOf hr)) (h a b)

/-- A relation identifying two distinct elements has a strictly smaller quotient. -/
theorem card_quotient_lt [Finite α] (hr : Equivalence r) {a b : α} (hab : a ≠ b)
    (hrab : r a b) : Nat.card (Quotient (setoidOf hr)) < Nat.card α := by
  classical
  have hnotinj : ¬ Function.Injective (Quotient.mk (setoidOf hr)) :=
    fun hinj => hab (hinj (Quotient.sound hrab))
  have : Fintype α := Fintype.ofFinite α
  have : Fintype (Quotient (setoidOf hr)) := Fintype.ofFinite _
  have hlt : Fintype.card (Quotient (setoidOf hr)) < Fintype.card α :=
    Fintype.card_lt_of_surjective_not_injective _ Quotient.mk_surjective hnotinj
  simpa only [Nat.card_eq_fintype_card] using hlt

end Quot

/-! ### Minimality and transport to `Fin n` -/

/-- Push an operation forward along a bijection of carriers. -/
def transportOp {β γ : Type*} (e : β ≃ γ) (op : β → β → β) : γ → γ → γ :=
  fun a b => e (op (e.symm a) (e.symm b))

/-- `E677` is invariant under transport of the carrier. -/
theorem e677_transportOp {β γ : Type*} (e : β ≃ γ) {op : β → β → β} (h : E677 op) :
    E677 (transportOp e op) := by
  intro i j
  have hij := congrArg e (h (e.symm i) (e.symm j))
  simpa [transportOp] using hij

/-- If every `E677` operation on `Fin n` with `n < N` satisfies `E255`, then every finite
`E677` magma with fewer than `N` elements satisfies `E255`. -/
theorem e255_of_card_lt {N : ℕ}
    (hmin : ∀ n : ℕ, n < N → ∀ op' : Fin n → Fin n → Fin n, E677 op' → E255 op')
    {β : Type*} [Finite β] (op : β → β → β) (h : E677 op) (hcard : Nat.card β < N) :
    E255 op := by
  intro x
  let e : β ≃ Fin (Nat.card β) := Finite.equivFin β
  have hx := hmin _ hcard (transportOp e op) (e677_transportOp e h) (e x)
  exact e.injective (by simpa [transportOp] using hx)

end AbelianHelpers

theorem solution
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n,
  FiniteMagmaE677.E677 op' → FiniteMagmaE677.E255 op')
(z : α) (hz : op (op (op z z) z) z ≠ z)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(habel : ∀ (k : ℕ) (p : (Fin (k + 1) → α) → α),
  (∀ T : ((Fin (k + 1) → α) → α) → Prop, (∀ i : Fin (k + 1), T (fun v => v i)) →
    (∀ f g : (Fin (k + 1) → α) → α, T f → T g → T (fun v => op (f v) (g v))) → T p) →
  ∀ (x y : α) (c d : Fin k → α), r x y → (∀ i : Fin k, r (c i) (d i)) →
    p (Fin.cons x c) = p (Fin.cons x d) → p (Fin.cons y c) = p (Fin.cons y d))
(a b : α) (hab : r a b) :
a = b := by
  classical
  by_contra hne
  -- The quotient `Q = α / r` is a smaller `E677` magma, so it satisfies `E255`; at the class
  -- of `z` this gives `r (q z) z`.
  have hQ255 : E255 (AbelianHelpers.quotOp op hr hcompat) :=
    AbelianHelpers.e255_of_card_lt hmin _ (AbelianHelpers.e677_quotOp h hr hcompat)
      (AbelianHelpers.card_quotient_lt hr hne hab)
  have hzq : r (op (op (op z z) z) z) z :=
    hr.symm (Quotient.exact (a := z) (b := op (op (op z z) z) z)
      (hQ255 (Quotient.mk (AbelianHelpers.setoidOf hr) z)))
  -- Row agreement: the term condition for the term `y ◇ x`, with `x` distinguished.
  have hRA : ∀ s s' t u : α, r s s' → r t u → op s t = op s' t → op s u = op s' u := by
    intro s s' t u hss' htu hst
    have hterm : ∀ T : ((Fin 2 → α) → α) → Prop, (∀ i : Fin 2, T (fun v => v i)) →
        (∀ f g : (Fin 2 → α) → α, T f → T g → T (fun v => op (f v) (g v))) →
          T (fun v => op (v 1) (v 0)) :=
      fun T hproj hop => hop _ _ (hproj 1) (hproj 0)
    simpa using habel 1 (fun v => op (v 1) (v 0)) hterm t u (fun _ => s) (fun _ => s') htu
      (fun _ => hss') (by simpa using hst)
  -- Row agreement over the class of `(z ◇ z) ◇ z` gives a fixer of `z`, so `q z = z`.
  exact hz (AbelianHelpers.eq255_from_fixer_exists h z
    (AbelianHelpers.exists_fixer_of_rowAgreementAt h hr hcompat hzq
      fun s s' hs hs' hsz u hu => hRA s s' z u (hr.trans (hr.symm hs) hs') hu hsz)).symm

#print axioms solution
