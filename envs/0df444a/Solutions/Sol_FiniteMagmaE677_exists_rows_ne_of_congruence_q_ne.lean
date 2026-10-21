-- Prove2me | solution 1 for FiniteMagmaE677.exists_rows_ne_of_congruence_q_ne
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-21T04:49:02.524126+00:00
-- url     : https://prove2.me/submissions/eb5259a7-194d-4a10-b8ca-461f2905158a

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# The fixer block of a point where `E255` fails

Let `op` be a finite `E677` magma and `r` a congruence of `op`.  Let `z` satisfy
`q z ≠ z` and `r (q z) z`, where `q z = ((z ◇ z) ◇ z) ◇ z`, and put `s = (z ◇ z) ◇ z`.
Then there are `a ≠ a'` in the class of `s` and `u` in the class of `z` with
`a ◇ z = a' ◇ z` and `a ◇ u ≠ a' ◇ u`.

## Proof

* Right multiplication by `z` maps the class of `s` into the class of `z`, since
  `r (s ◇ z) z`.
* Suppose that any two elements of the class of `s` with equal products with `z` have
  equal rows on the class of `z`.  Then `eq_of_rows_eq_on_class` makes this map injective.
  All classes have one size (`card_class_eq`), so the map is onto, and some `a` satisfies
  `a ◇ z = z` (`exists_fixer_of_rowAgreementAt`).  Such an `a` gives `q z = z`
  (`eq255_from_fixer_exists`), which is false.
* So two elements `a`, `a'` of the class of `s` have `a ◇ z = a' ◇ z` and rows that differ
  at some `u` in the class of `z`; then `a ≠ a'`.

The argument is the one of T. Tao (ETP Zulip thread "FINITE: 677 -> 255", 2024-12-14) for
extension models, in a pointwise form for one congruence.

Ported from `lean/E677/FixerBlock.lean`, `lean/E677/MonolithReduction.lean`,
`lean/E677/CoreBase.lean`, `lean/E677/Spine/CoreOrbit.lean` and
`lean/E677/Spine/Cancellation.lean` of a private repo (Adam McKenna).
-/

universe u
open FiniteMagmaE677

namespace FixerBlockHelpers

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

/-! ### The row-agreement lift -/

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

end FixerBlockHelpers

theorem solution
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(z : α) (hz : op (op (op z z) z) z ≠ z)
(hrz : r (op (op (op z z) z) z) z) :
∃ a a' u : α, r (op (op z z) z) a ∧ r (op (op z z) z) a' ∧ r z u ∧
  a ≠ a' ∧ op a z = op a' z ∧ op a u ≠ op a' u := by
  by_contra hcon
  push Not at hcon
  -- Without such `a`, `a'`, `u`, the row-agreement lift gives an element that sends `z`
  -- to `z`, and then `q z = z`.
  refine hz (FixerBlockHelpers.eq255_from_fixer_exists h z
    (FixerBlockHelpers.exists_fixer_of_rowAgreementAt h hr hcompat hrz
      fun a a' ha ha' hab u hu => ?_)).symm
  by_cases haa' : a = a'
  · rw [haa']
  · exact hcon a a' u ha ha' hu haa' hab

#print axioms solution
