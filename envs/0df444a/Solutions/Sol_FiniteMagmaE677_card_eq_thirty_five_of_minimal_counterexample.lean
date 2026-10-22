-- Prove2me | solution 1 for FiniteMagmaE677.card_eq_thirty_five_of_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-22T05:40:53.222137+00:00
-- url     : https://prove2.me/submissions/38d4b0c9-f389-40c0-a8e7-ea9a62a16a7a

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# A minimum-order counterexample of order 35 with a non-universal congruence

Let `op` be a finite `E677` magma failing `E255` at `z`, such that every `E677` magma on
`Fin n` with `n < |α|` satisfies `E255`.  Let `r` be a congruence of `op` that relates `z`
and `q z = ((z ◇ z) ◇ z) ◇ z` and is not the universal relation.  Assume that every
`E677` magma of order 7 has an idempotent.  If `|α| = 35`, then `α / r` has 7 elements,
the class of `z` has 5 elements, and some class is idempotent in `α / r`.

## Proof

* `card_facts` (the argument of the bound 24): for `Q = α / r` and the class size `m`,
  `|α| = |Q| · m`, `|Q| ≥ 6` and `m ≥ 4`.
* `35 = |Q| · m` with `|Q| ≥ 6` and `m ≥ 4` gives `|Q| = 7` and `m = 5`.
* `Q` is an `E677` magma of order 7, so the order-7 hypothesis gives an idempotent
  class.

The helpers before `card_facts` are those of the solution of Counterexample structure (b).
Ported from `lean/E677/MonolithOrderBound.lean`, `lean/E677/ClassThreeLift.lean`,
`lean/E677/MonolithReduction.lean`, `lean/E677/CriticalCore.lean` and
`lean/E677/Spine/Cancellation.lean` of a private repo (Adam McKenna).
-/

universe u
open FiniteMagmaE677

namespace ThirtyFiveEqHelpers

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

/-! ### The finite check on `Fin 3` -/

namespace ClassThree

/-- Decides `∀ x : Fin 3, P x` through its three instances.  It replaces the generic
instance in this file's finite check to shorten kernel reduction. -/
@[reducible] private def decForallFin3 {P : Fin 3 → Prop} [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (P 0 ∧ P 1 ∧ P 2)
    ⟨fun ⟨h0, h1, h2⟩ x => by fin_cases x <;> assumption, fun h => ⟨h 0, h 1, h 2⟩⟩

/-- Decides `∃ x : Fin 3, P x` through its three instances. -/
@[reducible] private def decExistsFin3 {P : Fin 3 → Prop} [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (P 0 ∨ P 1 ∨ P 2)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
      fun ⟨x, hx⟩ => by fin_cases x <;> simp_all⟩

attribute [local instance high] decForallFin3 decExistsFin3

/-- The entry at `i` of the triple `(a, b, c)`. -/
private def pick (a b c i : Fin 3) : Fin 3 :=
  if i.val = 0 then a else if i.val = 1 then b else c

/-- The table `Fin 3 → Fin 3 → Fin 3` whose entry at `(i, j)` is `aij`. -/
private def table (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Fin 3) (i j : Fin 3) : Fin 3 :=
  pick (pick a00 a01 a02 j) (pick a10 a11 a12 j) (pick a20 a21 a22 j) i

private theorem table_self (f : Fin 3 → Fin 3 → Fin 3) :
    table (f 0 0) (f 0 1) (f 0 2) (f 1 0) (f 1 1) (f 1 2) (f 2 0) (f 2 1) (f 2 2) = f := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The inverse of the row `σ v`, when that row is a permutation of `Fin 3`. -/
private def rowInv (σ : Fin 3 → Fin 3 → Fin 3) (v s : Fin 3) : Fin 3 :=
  if σ v 0 = s then 0 else if σ v 1 = s then 1 else 2

private theorem rowInv_spec (σ : Fin 3 → Fin 3 → Fin 3) (v s : Fin 3)
    (hσ : Function.Injective (σ v)) : σ v (rowInv σ v s) = s := by
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hσ s
  unfold rowInv
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · fin_cases x
    · exact absurd hx h0
    · exact absurd hx h1
    · exact hx

/-- (★) with `d` in place of `D (σ v x) v`: `σ v (E x d) = x`. -/
private def StarAt (σ E : Fin 3 → Fin 3 → Fin 3) (x v d : Fin 3) : Prop :=
  σ v (E x d) = x

private instance (σ E : Fin 3 → Fin 3 → Fin 3) (x v d : Fin 3) :
    Decidable (StarAt σ E x v d) := by
  unfold StarAt; infer_instance

/-- The table `D` recovered from the table `D' x v = D (σ v x) v`. -/
private def unshift (σ D' : Fin 3 → Fin 3 → Fin 3) (s v : Fin 3) : Fin 3 :=
  D' (rowInv σ v s) v

/-- Every row of `D` is injective. -/
private def RowsInjective (D : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x a b, D x a = D x b → a = b

private instance (D : Fin 3 → Fin 3 → Fin 3) : Decidable (RowsInjective D) := by
  unfold RowsInjective; infer_instance

/-- Some `v` satisfies `E y (D x v) = x` for all `x` and `y`. -/
private def HasCommonPreimage (E D : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∃ v, ∀ x y, E y (D x v) = x

private instance (E D : Fin 3 → Fin 3 → Fin 3) : Decidable (HasCommonPreimage E D) := by
  unfold HasCommonPreimage; infer_instance

/-! The finite statement is split into nested layers so that instance search stays
small and the kernel prunes each branch as soon as a hypothesis fails.  The entry
`dxv` stands for `D (σ v x) v`. -/

/-- Third layer: the entries `d2v`, then the conclusion. -/
private def CheckD2 (σ E : Fin 3 → Fin 3 → Fin 3) (d00 d01 d02 d10 d11 d12 : Fin 3) : Prop :=
  ∀ d20, StarAt σ E 2 0 d20 → ∀ d21, StarAt σ E 2 1 d21 → ∀ d22, StarAt σ E 2 2 d22 →
    RowsInjective (unshift σ (table d00 d01 d02 d10 d11 d12 d20 d21 d22)) →
      HasCommonPreimage E (unshift σ (table d00 d01 d02 d10 d11 d12 d20 d21 d22))

private instance (σ E : Fin 3 → Fin 3 → Fin 3) (d00 d01 d02 d10 d11 d12 : Fin 3) :
    Decidable (CheckD2 σ E d00 d01 d02 d10 d11 d12) := by
  unfold CheckD2; infer_instance

/-- Second layer: the entries `d1v`. -/
private def CheckD1 (σ E : Fin 3 → Fin 3 → Fin 3) (d00 d01 d02 : Fin 3) : Prop :=
  ∀ d10, StarAt σ E 1 0 d10 → ∀ d11, StarAt σ E 1 1 d11 → ∀ d12, StarAt σ E 1 2 d12 →
    CheckD2 σ E d00 d01 d02 d10 d11 d12

private instance (σ E : Fin 3 → Fin 3 → Fin 3) (d00 d01 d02 : Fin 3) :
    Decidable (CheckD1 σ E d00 d01 d02) := by
  unfold CheckD1; infer_instance

/-- First layer: the entries `d0v`. -/
private def CheckD0 (σ E : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ d00, StarAt σ E 0 0 d00 → ∀ d01, StarAt σ E 0 1 d01 → ∀ d02, StarAt σ E 0 2 d02 →
    CheckD1 σ E d00 d01 d02

private instance (σ E : Fin 3 → Fin 3 → Fin 3) : Decidable (CheckD0 σ E) := by
  unfold CheckD0; infer_instance

/-- The rows `E 1` and `E 2` are injective; the row `E 0` is the identity. -/
private def CheckE (σ : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ e10 e11 : Fin 3, e11 ≠ e10 → ∀ e12 : Fin 3, e12 ≠ e10 → e12 ≠ e11 →
  ∀ e20 e21 : Fin 3, e21 ≠ e20 → ∀ e22 : Fin 3, e22 ≠ e20 → e22 ≠ e21 →
    CheckD0 σ (table 0 1 2 e10 e11 e12 e20 e21 e22)

private instance (σ : Fin 3 → Fin 3 → Fin 3) : Decidable (CheckE σ) := by
  unfold CheckE; infer_instance

/-- The rows of `σ` are injective and none of them fixes `0`. -/
private def CheckSigma : Prop :=
  ∀ s00 : Fin 3, s00 ≠ 0 → ∀ s01 : Fin 3, s01 ≠ s00 → ∀ s02 : Fin 3, s02 ≠ s00 → s02 ≠ s01 →
  ∀ s10 : Fin 3, s10 ≠ 0 → ∀ s11 : Fin 3, s11 ≠ s10 → ∀ s12 : Fin 3, s12 ≠ s10 → s12 ≠ s11 →
  ∀ s20 : Fin 3, s20 ≠ 0 → ∀ s21 : Fin 3, s21 ≠ s20 → ∀ s22 : Fin 3, s22 ≠ s20 → s22 ≠ s21 →
    CheckE (table s00 s01 s02 s10 s11 s12 s20 s21 s22)

private instance : Decidable CheckSigma := by
  unfold CheckSigma; infer_instance

/-- The finite statement, checked by kernel reduction (`decide +kernel`). -/
private theorem checkSigma_holds : CheckSigma := by
  decide +kernel

/-- The finite step on `Fin 3`, with the fixed-point-free point at `0` and `E 0` the
identity. -/
theorem fin3_exists_common_preimage (σ D E : Fin 3 → Fin 3 → Fin 3)
    (hσ : ∀ v, Function.Injective (σ v)) (hD : ∀ x, Function.Injective (D x))
    (hE : ∀ x, Function.Injective (E x)) (hE0 : ∀ u, E 0 u = u)
    (hstar : ∀ x v, σ v (E x (D (σ v x) v)) = x) (hfix : ∀ v, σ v 0 ≠ 0) :
    ∃ v₀, ∀ x y, E y (D x v₀) = x := by
  have h0 := checkSigma_holds
    (σ 0 0) (hfix 0) (σ 0 1) ((hσ 0).ne (by decide))
    (σ 0 2) ((hσ 0).ne (by decide)) ((hσ 0).ne (by decide))
    (σ 1 0) (hfix 1) (σ 1 1) ((hσ 1).ne (by decide))
    (σ 1 2) ((hσ 1).ne (by decide)) ((hσ 1).ne (by decide))
    (σ 2 0) (hfix 2) (σ 2 1) ((hσ 2).ne (by decide))
    (σ 2 2) ((hσ 2).ne (by decide)) ((hσ 2).ne (by decide))
  rw [table_self σ] at h0
  have h1 := h0
    (E 1 0) (E 1 1) ((hE 1).ne (by decide)) (E 1 2) ((hE 1).ne (by decide))
    ((hE 1).ne (by decide))
    (E 2 0) (E 2 1) ((hE 2).ne (by decide)) (E 2 2) ((hE 2).ne (by decide))
    ((hE 2).ne (by decide))
  have hEt : table 0 1 2 (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) = E := by
    have h := table_self E
    rwa [hE0 0, hE0 1, hE0 2] at h
  rw [hEt] at h1
  have h2 := h1
    (D (σ 0 0) 0) (hstar 0 0) (D (σ 1 0) 1) (hstar 0 1) (D (σ 2 0) 2) (hstar 0 2)
    (D (σ 0 1) 0) (hstar 1 0) (D (σ 1 1) 1) (hstar 1 1) (D (σ 2 1) 2) (hstar 1 2)
    (D (σ 0 2) 0) (hstar 2 0) (D (σ 1 2) 1) (hstar 2 1) (D (σ 2 2) 2) (hstar 2 2)
  have ht : table (D (σ 0 0) 0) (D (σ 1 0) 1) (D (σ 2 0) 2) (D (σ 0 1) 0) (D (σ 1 1) 1)
      (D (σ 2 1) 2) (D (σ 0 2) 0) (D (σ 1 2) 1) (D (σ 2 2) 2) = fun x v => D (σ v x) v :=
    table_self fun x v => D (σ v x) v
  have hDt : unshift σ (fun x v => D (σ v x) v) = D := by
    funext s v
    change D (σ v (rowInv σ v s)) v = D s v
    rw [rowInv_spec σ v s (hσ v)]
  rw [ht, hDt] at h2
  exact h2 fun x _ _ hab => hD x hab

end ClassThree

/-! ### The common-preimage step -/

/--
Let `X`, `V`, `U` have three elements each, and let `σ_v : X → X` (`v ∈ V`),
`D_x : V → U` and `E_x : U → X` (`x ∈ X`) be injective.  Suppose that
`σ_v (E_x (D_{σ_v x} v)) = x` for all `x` and `v`, and that no `σ_v` fixes the point `t`.
Then some `v₀ ∈ V` satisfies `E_y (D_x v₀) = x` for all `x, y ∈ X`.
-/
theorem exists_common_preimage_of_no_fixed_point {X V U : Type*}
    [Finite X] [Finite V] [Finite U]
    (hX : Nat.card X = 3) (hV : Nat.card V = 3) (hU : Nat.card U = 3)
    (σ : V → X → X) (D : X → V → U) (E : X → U → X)
    (hσ : ∀ v, Function.Injective (σ v)) (hD : ∀ x, Function.Injective (D x))
    (hE : ∀ x, Function.Injective (E x))
    (hstar : ∀ x v, σ v (E x (D (σ v x) v)) = x) {t : X} (hfix : ∀ v, σ v t ≠ t) :
    ∃ v₀, ∀ x y, E y (D x v₀) = x := by
  classical
  -- Coordinates on `X` that send `t` to `0`.
  let e₀ : X ≃ Fin 3 := Finite.equivFinOfCardEq hX
  let eX : X ≃ Fin 3 := e₀.trans (Equiv.swap (e₀ t) 0)
  have heXt : eX t = 0 := by simp [eX]
  have heX0 : eX.symm 0 = t := eX.symm_apply_eq.mpr heXt.symm
  let eV : V ≃ Fin 3 := Finite.equivFinOfCardEq hV
  -- Coordinates on `U` through the bijection `E t : U → X`.
  have hEt : Function.Bijective (E t) := (hE t).bijective_of_nat_card_le (hX.trans hU.symm).le
  let eU : U ≃ Fin 3 := (Equiv.ofBijective (E t) hEt).trans eX
  obtain ⟨i₀, hi₀⟩ := ClassThree.fin3_exists_common_preimage
    (fun i j => eX (σ (eV.symm i) (eX.symm j)))
    (fun i j => eU (D (eX.symm i) (eV.symm j)))
    (fun i j => eX (E (eX.symm i) (eU.symm j)))
    (fun _ => eX.injective.comp ((hσ _).comp eX.symm.injective))
    (fun _ => eU.injective.comp ((hD _).comp eV.symm.injective))
    (fun _ => eX.injective.comp ((hE _).comp eU.symm.injective))
    (fun j => by
      rw [heX0]
      simp [eU, Equiv.ofBijective_apply_symm_apply])
    (fun i j => by simp [hstar])
    (fun i h => hfix (eV.symm i) (eX.injective (by
      have h' : eX (σ (eV.symm i) (eX.symm 0)) = 0 := h
      rw [heX0] at h'
      rw [h', heXt])))
  refine ⟨eV.symm i₀, fun x y => eX.injective ?_⟩
  simpa using hi₀ (eX x) (eX y)

/-! ### The fixer step -/

section Fixer

variable {α : Type*} [Finite α] {op : α → α → α}

local infixl:70 " ◇ " => op

/--
Let every class of the congruence `r` of a finite `E677` magma have three elements, and
let `r (s ◇ b) b`.  Then some `a` satisfies `a ◇ b = b`.
-/
theorem exists_fixer_of_card_class_eq_three (h : E677 op) {r : α → α → Prop}
    (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
    (h3 : ∀ a : α, Nat.card {x : α // r a x} = 3) {s b : α} (hsb : r (s ◇ b) b) :
    ∃ a : α, a ◇ b = b := by
  have compat : ∀ {a a' b b' : α}, r a a' → r b b' → r (a ◇ b) (a' ◇ b') :=
    fun h1 h2 => hcompat _ _ _ _ h1 h2
  by_contra hno
  push Not at hno
  -- `r (b ◇ (b ◇ s)) b`: `E677` at `(b, s)` and left cancellation of `s` modulo `r`.
  have hu : r (b ◇ (b ◇ s)) b := by
    apply rel_of_rel_mul_left h hr hcompat (y := s)
    have h1 : r (s ◇ (b ◇ ((s ◇ b) ◇ s))) (s ◇ (b ◇ (b ◇ s))) :=
      compat (hr.refl s) (compat (hr.refl b) (compat hsb (hr.refl s)))
    rw [← h b s] at h1
    exact hr.trans (hr.symm h1) (hr.symm hsb)
  have hσmem : ∀ v x : α, r s v → r b x → r b (v ◇ x) := fun v x hv hx =>
    hr.symm (hr.trans (compat (hr.symm hv) (hr.symm hx)) hsb)
  have hEmem : ∀ x u : α, r b x → r (b ◇ s) u → r b (x ◇ u) := fun x u hx hu' =>
    hr.symm (hr.trans (compat (hr.symm hx) (hr.symm hu')) hu)
  obtain ⟨v₀, hv₀⟩ := exists_common_preimage_of_no_fixed_point
    (X := {x : α // r b x}) (V := {x : α // r s x}) (U := {x : α // r (b ◇ s) x})
    (h3 b) (h3 s) (h3 (b ◇ s))
    (fun v x => ⟨v.1 ◇ x.1, hσmem v.1 x.1 v.2 x.2⟩)
    (fun x v => ⟨x.1 ◇ v.1, compat x.2 v.2⟩)
    (fun x u => ⟨x.1 ◇ u.1, hEmem x.1 u.1 x.2 u.2⟩)
    (fun v _ _ hvw => Subtype.ext (left_cancel h v.1 (congrArg Subtype.val hvw)))
    (fun x _ _ hvw => Subtype.ext (left_cancel h x.1 (congrArg Subtype.val hvw)))
    (fun x _ _ hvw => Subtype.ext (left_cancel h x.1 (congrArg Subtype.val hvw)))
    (fun x v => Subtype.ext (h x.1 v.1).symm)
    (t := ⟨b, hr.refl b⟩)
    (fun v hvb => hno v.1 (congrArg Subtype.val hvb))
  -- `(y ◇ x) ◇ y = v₀` on the class of `b`.
  have key : ∀ x y : α, r b x → r b y → (y ◇ x) ◇ y = v₀.1 := by
    intro x y hx hy
    have h1 : y ◇ (x ◇ v₀.1) = x := congrArg Subtype.val (hv₀ ⟨x, hx⟩ ⟨y, hy⟩)
    exact left_cancel h x (left_cancel h y ((h x y).symm.trans h1.symm))
  -- A second element `c` of the class of `b`.
  have : Nontrivial {x : α // r b x} :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h3 b]; norm_num)
  obtain ⟨⟨c, hc⟩, hcb⟩ := exists_ne (⟨b, hr.refl b⟩ : {x : α // r b x})
  -- Left translation by `c` maps the class of `b` onto the class of `b ◇ b`.
  let f : {x : α // r b x} → {x : α // r (b ◇ b) x} :=
    fun x => ⟨c ◇ x.1, compat hc x.2⟩
  have hf : Function.Injective f := fun _ _ hxy =>
    Subtype.ext (left_cancel h c (congrArg Subtype.val hxy))
  obtain ⟨⟨x, hx⟩, hfx⟩ :=
    (hf.bijective_of_nat_card_le ((h3 (b ◇ b)).trans (h3 b).symm).le).2
      ⟨b ◇ b, hr.refl _⟩
  have hcx : c ◇ x = b ◇ b := congrArg Subtype.val hfx
  have hbb := key b b (hr.refl b) (hr.refl b)
  have hcc := key x c hx hc
  rw [hcx] at hcc
  exact hcb (Subtype.ext (left_cancel h (b ◇ b) (hcc.trans hbb.symm)))

/-- If every class of a congruence `r` of a finite `E677` magma has three elements and
`E255` holds modulo `r`, then `E255` holds. -/
theorem e255_of_card_class_eq_three (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
    (h3 : ∀ a : α, Nat.card {x : α // r a x} = 3)
    (hquot : ∀ x : α, r (((x ◇ x) ◇ x) ◇ x) x) : E255 op := fun z =>
  eq255_from_fixer_exists h z (exists_fixer_of_card_class_eq_three h hr hcompat h3 (hquot z))

/-! ### Class sizes -/

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

/-! ### The two-element lift -/

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

/-- If the class of `b` has two elements, the class of `s` has at least two elements, and
`r (s ◇ b) b`, then some `a` satisfies `a ◇ b = b`. -/
theorem exists_fixer_of_card_class_eq_two (h : E677 op) {r : α → α → Prop}
    (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
    {s b : α} (hb : Nat.card {x : α // r b x} = 2)
    (hs : 1 < Nat.card {x : α // r s x}) (hsb : r (s ◇ b) b) :
    ∃ a : α, a ◇ b = b := by
  have compat : ∀ {a a' b b' : α}, r a a' → r b b' → r (a ◇ b) (a' ◇ b') :=
    fun h1 h2 => hcompat _ _ _ _ h1 h2
  by_contra hno
  push Not at hno
  -- The other element `b₁` of the class of `b`.
  obtain ⟨⟨b₁, hbb₁⟩, hb₁, hV⟩ :=
    (Nat.card_eq_two_iff' (⟨b, hr.refl b⟩ : {x : α // r b x})).mp hb
  have hb₁ne : b₁ ≠ b := fun hbe => hb₁ (Subtype.ext hbe)
  have hclass : ∀ y : α, r b y → y = b ∨ y = b₁ := by
    intro y hy
    by_cases hyb : y = b
    · exact Or.inl hyb
    · exact Or.inr (congrArg Subtype.val
        (hV ⟨y, hy⟩ fun hye => hyb (congrArg Subtype.val hye)))
  -- Every row in the class of `s` swaps `b` and `b₁`.
  have hrow : ∀ a : α, r s a → a ◇ b = b₁ ∧ a ◇ b₁ = b := by
    intro a ha
    have hab : r b (a ◇ b) :=
      hr.symm (hr.trans (compat (hr.symm ha) (hr.refl b)) hsb)
    have h1 : a ◇ b = b₁ := (hclass _ hab).resolve_left (hno a)
    have hab₁ : r b (a ◇ b₁) :=
      hr.symm (hr.trans (compat (hr.symm ha) (hr.symm hbb₁)) hsb)
    refine ⟨h1, (hclass _ hab₁).resolve_right fun hab' => hb₁ne ?_⟩
    exact (left_cancel h a (h1.trans hab'.symm)).symm
  -- Two distinct elements of the class of `s`.
  have : Nontrivial {x : α // r s x} := Finite.one_lt_card_iff_nontrivial.mp hs
  obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, hne⟩ := exists_pair_ne {x : α // r s x}
  apply hne
  have ha₁b : r (a₁ ◇ b) b := hr.trans (compat (hr.symm ha₁) (hr.refl b)) hsb
  have hrows : ∀ y : α, r b y → a₁ ◇ y = a₂ ◇ y := by
    intro y hy
    rcases hclass y hy with rfl | rfl
    · exact (hrow a₁ ha₁).1.trans (hrow a₂ ha₂).1.symm
    · exact (hrow a₁ ha₁).2.trans (hrow a₂ ha₂).2.symm
  exact Subtype.ext
    (eq_of_rows_eq_on_class h hr hcompat (hr.trans (hr.symm ha₁) ha₂) ha₁b hrows)

/-- If every class of a congruence `r` of a finite `E677` magma has two elements and
`E255` holds modulo `r`, then `E255` holds. -/
theorem e255_of_card_class_eq_two (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
    (h2 : ∀ a : α, Nat.card {x : α // r a x} = 2)
    (hquot : ∀ x : α, r (((x ◇ x) ◇ x) ◇ x) x) : E255 op := fun z =>
  eq255_from_fixer_exists h z
    (exists_fixer_of_card_class_eq_two h hr hcompat (h2 z) (by rw [h2]; norm_num) (hquot z))

/-! ### Left periods of a non-idempotent point satisfying `E255` -/

/-- `L_t²(t) = t` forces `t ◇ t = t`. -/
theorem self_mul_eq_self_of_period_two (h : E677 op) {t : α}
    (hper : t ◇ (t ◇ t) = t) : t ◇ t = t := by
  have hΦ : (t ◇ t) ◇ t = t :=
    left_cancel h t (left_cancel h t ((h t t).symm.trans hper.symm))
  exact (fixer_unique h hΦ).trans hΦ

/-- `L_t³(t) = t` forces `t ◇ t = t`. -/
theorem self_mul_eq_self_of_period_three (h : E677 op) (x : α)
    (hper : x ◇ (x ◇ (x ◇ x)) = x) : x ◇ x = x := by
  have h1 : (x ◇ x) ◇ x = x ◇ x :=
    left_cancel h x (left_cancel h x ((h x x).symm.trans hper.symm))
  have h2 : (x ◇ (x ◇ x)) ◇ (x ◇ x) = x ◇ x := by
    have hE := h (x ◇ (x ◇ x)) x
    rw [hper] at hE
    exact left_cancel h x hE.symm
  have h3 := fixer_unique h h2
  have h4 : x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    have hbr := backward_recurrence h x (x ◇ x)
    rw [h1, ← h3] at hbr
    exact hbr
  have h5 : (x ◇ x) ◇ (x ◇ x) = x ◇ x := by
    have hE := h x (x ◇ x)
    rw [h1] at hE
    exact left_cancel h x (left_cancel h (x ◇ x) (hE.symm.trans h4))
  rw [h5, h5] at h3
  exact left_cancel h x h3

/-- `L_t⁴(t) = t` and `E255` at `t` force `t ◇ t = t`. -/
theorem self_mul_eq_self_of_period_four (h : E677 op) {t : α}
    (ht : ((t ◇ t) ◇ t) ◇ t = t) (hper : t ◇ (t ◇ (t ◇ (t ◇ t))) = t) : t ◇ t = t := by
  have hΦ : (t ◇ t) ◇ t = t ◇ (t ◇ t) :=
    left_cancel h t (left_cancel h t ((h t t).symm.trans hper.symm))
  have hc₂ : (t ◇ (t ◇ t)) ◇ t = t := by
    rw [← hΦ]
    exact ht
  have hrec := backward_recurrence h t t
  rw [hc₂, hΦ] at hrec
  exact self_mul_eq_self_of_period_two h hrec.symm

/-- `L_t⁵(t) = t` and `E255` at `t` and at `t ◇ t` force `t ◇ t = t`. -/
theorem self_mul_eq_self_of_period_five (h : E677 op) {t : α}
    (ht : ((t ◇ t) ◇ t) ◇ t = t)
    (ht₁ : (((t ◇ t) ◇ (t ◇ t)) ◇ (t ◇ t)) ◇ (t ◇ t) = t ◇ t)
    (hper : t ◇ (t ◇ (t ◇ (t ◇ (t ◇ t)))) = t) : t ◇ t = t := by
  have hΦ : (t ◇ t) ◇ t = t ◇ (t ◇ (t ◇ t)) :=
    left_cancel h t (left_cancel h t ((h t t).symm.trans hper.symm))
  have hc₃ : (t ◇ (t ◇ (t ◇ t))) ◇ t = t := by
    rw [← hΦ]
    exact ht
  -- Backward recurrence at index one: `c₁ = c₂ ◇ (c₃ ◇ t) = c₂ ◇ t`.
  have hrec₁ := backward_recurrence h (t ◇ t) t
  rw [hc₃] at hrec₁
  -- Backward recurrence at index zero: `t = c₁ ◇ (c₂ ◇ t) = c₁ ◇ c₁`.
  have hrec₀ := backward_recurrence h t t
  rw [← hrec₁] at hrec₀
  -- `E255` at `c₁`.
  have h₁ := ht₁
  rw [← hrec₀] at h₁
  have h₂ : (t ◇ (t ◇ t)) ◇ (t ◇ t) = (t ◇ (t ◇ t)) ◇ t := h₁.trans hrec₁
  exact left_cancel h _ h₂

/-- In a finite `E677` magma, let `t ◇ t ≠ t`, and let `E255` hold at `t` and at `t ◇ t`.
Then every `n > 0` with `L_t^n(t) = t` satisfies `n ≥ 6`. -/
theorem six_le_of_iterate_eq_self (h : E677 op) {t : α} (hidem : t ◇ t ≠ t)
    (ht : ((t ◇ t) ◇ t) ◇ t = t)
    (ht₁ : (((t ◇ t) ◇ (t ◇ t)) ◇ (t ◇ t)) ◇ (t ◇ t) = t ◇ t) {n : ℕ} (hn : 0 < n)
    (hper : (fun y => t ◇ y)^[n] t = t) : 6 ≤ n := by
  by_contra hlt
  push Not at hlt
  interval_cases n
  · exact hidem hper
  · exact hidem (self_mul_eq_self_of_period_two h hper)
  · exact hidem (self_mul_eq_self_of_period_three h t hper)
  · exact hidem (self_mul_eq_self_of_period_four h ht hper)
  · exact hidem (self_mul_eq_self_of_period_five h ht ht₁ hper)

/-- A finite `E677` magma satisfying `E255` that has a non-idempotent element `t` has at
least six elements: `L_tⁱ(t)` for `i < 6` are pairwise distinct. -/
theorem six_le_card_of_e255 (h : E677 op) (h255 : E255 op) {t : α} (hidem : t ◇ t ≠ t) :
    6 ≤ Nat.card α := by
  have hq : ∀ x : α, ((x ◇ x) ◇ x) ◇ x = x := fun x => (h255 x).symm
  have key : ∀ i j : ℕ, i < j → j < 6 →
      (fun y => t ◇ y)^[i] t ≠ (fun y => t ◇ y)^[j] t := by
    intro i j hij hj heq
    have hshift : (fun y => t ◇ y)^[i] t =
        (fun y => t ◇ y)^[i] ((fun y => t ◇ y)^[j - i] t) := by
      rw [heq, ← Function.iterate_add_apply, Nat.add_sub_cancel' hij.le]
    have hback := ((leftMul_inj h t).iterate i) hshift
    have h6 := six_le_of_iterate_eq_self h hidem (hq t) (hq (t ◇ t))
      (Nat.sub_pos_of_lt hij) hback.symm
    omega
  have hinj : Function.Injective fun i : Fin 6 => (fun y => t ◇ y)^[i.1] t := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact key i j hlt j.2 hij
    · exact key j i hlt i.2 hij.symm
  simpa using Nat.card_le_card_of_injective _ hinj

end Fixer

/-! ### Quotients by a compatible reflexive, symmetric and transitive relation -/

section Quot

variable {α : Type*} {r : α → α → Prop}

/-- The setoid of a reflexive, symmetric and transitive relation. -/
abbrev setoidOf (hr : Equivalence r) : Setoid α := ⟨r, hr⟩

/-- The operation induced on the quotient by a compatible reflexive, symmetric and transitive relation. -/
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

/-- If every class of `r` has `m` elements, then `|α| = |α/r| · m`. -/
theorem card_eq_card_quotient_mul [Finite α] (hr : Equivalence r) (m : ℕ)
    (hm : ∀ a : α, Nat.card {x : α // r a x} = m) :
    Nat.card α = Nat.card (Quotient (setoidOf hr)) * m := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype (Quotient (setoidOf hr)) := Fintype.ofFinite _
  have hfib : ∀ c : Quotient (setoidOf hr),
      Nat.card {x : α // Quotient.mk (setoidOf hr) x = c} = m := by
    intro c
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective c
    rw [← hm a]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun hx => hr.symm (Quotient.exact hx), fun hx => Quotient.sound (hr.symm hx)⟩)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (setoidOf hr))),
    Nat.card_sigma, Finset.sum_congr rfl fun c _ => hfib c, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end Quot

/-! ### Minimality and transport to `Fin n` -/

/-- Push an operation forward along a bijection of carriers. -/
def transportOp {β γ : Type*} (e : β ≃ γ) (op : β → β → β) : γ → γ → γ :=
  fun a b => e (op (e.symm a) (e.symm b))

/-- If every `E677` operation on `Fin n` with `n < N` satisfies `E255`, then every finite
`E677` magma with fewer than `N` elements satisfies `E255`. -/
theorem e255_of_card_lt {N : ℕ}
    (hmin : ∀ n : ℕ, n < N → ∀ op' : Fin n → Fin n → Fin n, E677 op' → E255 op')
    {β : Type*} [Finite β] (op : β → β → β) (h : E677 op) (hcard : Nat.card β < N) :
    E255 op := by
  intro x
  let e : β ≃ Fin (Nat.card β) := Finite.equivFin β
  have h' : E677 (transportOp e op) := by
    intro i j
    have hij := congrArg e (h (e.symm i) (e.symm j))
    simpa [transportOp] using hij
  have hx := hmin _ hcard (transportOp e op) h' (e x)
  exact e.injective (by simpa [transportOp] using hx)

/-- `GeneratedBy op z a` holds when `a` is an `op`-term in the single generator `z`. -/
inductive GeneratedBy {α : Type*} (op : α → α → α) (z : α) : α → Prop
  | base : GeneratedBy op z z
  | mul {a b : α} : GeneratedBy op z a → GeneratedBy op z b → GeneratedBy op z (op a b)

/-- The operation of the submagma generated by `z`. -/
def genOp {α : Type*} (op : α → α → α) (z : α) :
    {a : α // GeneratedBy op z a} → {a : α // GeneratedBy op z a} →
      {a : α // GeneratedBy op z a} :=
  fun a b => ⟨op a.1 b.1, GeneratedBy.mul a.2 b.2⟩

/-- A finite `E677` magma failing `E255` at `z`, all of whose smaller relatives satisfy
`E255`, is generated by `z`. -/
theorem generatedBy_of_minimal {α : Type*} [Finite α] {op : α → α → α} (h : E677 op)
    (hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n, E677 op' → E255 op')
    {z : α} (hz : op (op (op z z) z) z ≠ z) (w : α) : GeneratedBy op z w := by
  by_contra hw
  have hS : E677 (genOp op z) := fun a b => Subtype.ext (h a.1 b.1)
  have h255 := e255_of_card_lt hmin (genOp op z) hS (Finite.card_subtype_lt hw)
  exact hz (congrArg Subtype.val (h255 ⟨z, GeneratedBy.base⟩)).symm

/-! ### Small-order facts and idempotent classes -/

/-- `E677` is invariant under transport of the carrier. -/
theorem e677_transportOp {β γ : Type*} (e : β ≃ γ) {op : β → β → β} (h : E677 op) :
    E677 (transportOp e op) := by
  intro i j
  have hij := congrArg e (h (e.symm i) (e.symm j))
  simpa [transportOp] using hij

/-- If no `E677` operation on `Fin k` exists, no finite `E677` magma has `k` elements. -/
theorem card_ne_of_no_e677 {β : Type*} [Finite β] {op : β → β → β} (h : E677 op) {k : ℕ}
    (hk : ∀ op' : Fin k → Fin k → Fin k, ¬ E677 op') : Nat.card β ≠ k := by
  rintro rfl
  exact hk _ (e677_transportOp (Finite.equivFin β) h)

/-- If every `E677` operation on `Fin k` has an idempotent, every finite `E677` magma with
`k` elements has an idempotent. -/
theorem exists_idempotent_of_card {β : Type*} [Finite β] {op : β → β → β} (h : E677 op)
    {k : ℕ} (hk : ∀ op' : Fin k → Fin k → Fin k, E677 op' → ∃ x : Fin k, op' x x = x)
    (hcard : Nat.card β = k) : ∃ x : β, op x x = x := by
  subst hcard
  obtain ⟨x, hx⟩ := hk _ (e677_transportOp (Finite.equivFin β) h)
  refine ⟨(Finite.equivFin β).symm x, ?_⟩
  have hx' : Finite.equivFin β
      (op ((Finite.equivFin β).symm x) ((Finite.equivFin β).symm x)) = x := hx
  simpa using congrArg (Finite.equivFin β).symm hx'

/-- The operation on the class of `e` when `r (op e e) e`: for `a` and `b` in the class of
`e`, `op a b` is in the class of `op e e`, which is the class of `e`. -/
def classOp {α : Type*} (op : α → α → α) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) (e : α)
    (he : r (op e e) e) : {x : α // r e x} → {x : α // r e x} → {x : α // r e x} :=
  fun a b => ⟨op a.1 b.1, hr.trans (hr.symm he) (hcompat _ _ _ _ a.2 b.2)⟩

/-- The class of `e` with `r (op e e) e` is an `E677` magma. -/
theorem e677_classOp {α : Type*} {op : α → α → α} (h : E677 op) {r : α → α → Prop}
    (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b')) (e : α)
    (he : r (op e e) e) : E677 (classOp op hr hcompat e he) :=
  fun a b => Subtype.ext (h a.1 b.1)

/-- If no class of `r` is idempotent in the quotient, and every `E677` operation on `Fin k`
has an idempotent, then the quotient does not have `k` elements. -/
theorem card_quotient_ne_of_no_idempotent {α : Type*} [Finite α] {op : α → α → α}
    (h : E677 op) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
    (hI : ∀ e : α, ¬ r (op e e) e) {k : ℕ}
    (hk : ∀ op' : Fin k → Fin k → Fin k, E677 op' → ∃ x : Fin k, op' x x = x) :
    Nat.card (Quotient (setoidOf hr)) ≠ k := by
  intro hQk
  obtain ⟨c, hc⟩ := exists_idempotent_of_card (e677_quotOp h hr hcompat) hk hQk
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective c
  exact hI e (Quotient.exact (a := op e e) (b := e) hc)

/-- The only factorization `a · b = 35` with `a ≥ 6` and `b ≥ 4` is `7 · 5`. -/
theorem eq_seven_and_eq_five_of_mul_eq {a b : ℕ} (h : a * b = 35) (ha : 6 ≤ a)
    (hb : 4 ≤ b) : a = 7 ∧ b = 5 := by
  have ha' : a ≤ 8 := by nlinarith
  have hb' : b ≤ 5 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega

/-! ### Sizes for a minimum-order counterexample with a non-universal congruence -/

/-- Let `op` be a finite `E677` magma failing `E255` at `z`, such that every `E677` magma
on `Fin n` with `n < |α|` satisfies `E255`, and let `r` be a congruence that relates `z`
and `q z` and is not the universal relation.  Then `|α| = |α/r| · m`, `|α/r| ≥ 6` and
`m ≥ 4`, where `m` is the size of the class of `z`.  This is the argument of the bound 24
(Counterexample structure (b)). -/
theorem card_facts {α : Type*} [Finite α] {op : α → α → α} (h : E677 op)
    (hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n, E677 op' → E255 op')
    {z : α} (hz : op (op (op z z) z) z ≠ z) {r : α → α → Prop} (hr : Equivalence r)
    (hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
    (hrz : r z (op (op (op z z) z) z)) (hproper : ∃ a b : α, ¬ r a b) :
    Nat.card α = Nat.card (Quotient (setoidOf hr)) * Nat.card {x : α // r z x} ∧
      6 ≤ Nat.card (Quotient (setoidOf hr)) ∧ 4 ≤ Nat.card {x : α // r z x} := by
  classical
  -- The quotient `Q = α / r` is a smaller `E677` magma, so it satisfies `E255`.
  have hQ677 : E677 (quotOp op hr hcompat) := e677_quotOp h hr hcompat
  have hlt : Nat.card (Quotient (setoidOf hr)) < Nat.card α :=
    card_quotient_lt hr (fun hzq => hz hzq.symm) hrz
  have hQ255 : E255 (quotOp op hr hcompat) := e255_of_card_lt hmin _ hQ677 hlt
  have hquot : ∀ x : α, r (op (op (op x x) x) x) x := by
    intro x
    have hx : r x (op (op (op x x) x) x) :=
      Quotient.exact (a := x) (b := op (op (op x x) x) x)
        (hQ255 (Quotient.mk (setoidOf hr) x))
    exact hr.symm hx
  -- All classes have the size `m` of the class of `z`, and `|α| = |Q| · m`.
  have hm : ∀ a : α, Nat.card {x : α // r a x} = Nat.card {x : α // r z x} :=
    fun a => card_class_eq h hr hcompat a z
  have hcard := card_eq_card_quotient_mul hr _ hm
  have hm2 : 1 < Nat.card {x : α // r z x} :=
    Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨z, hr.refl z⟩, ⟨_, hrz⟩,
      fun he => hz (congrArg Subtype.val he).symm⟩⟩
  have hne2 : Nat.card {x : α // r z x} ≠ 2 := fun h2 =>
    hz (e255_of_card_class_eq_two h hr hcompat (fun a => (hm a).trans h2) hquot z).symm
  have hne3 : Nat.card {x : α // r z x} ≠ 3 := fun h3 =>
    hz (e255_of_card_class_eq_three h hr hcompat (fun a => (hm a).trans h3) hquot z).symm
  -- The class of `z` is not idempotent in the quotient.
  have hidem : quotOp op hr hcompat (Quotient.mk (setoidOf hr) z)
      (Quotient.mk (setoidOf hr) z) ≠ Quotient.mk (setoidOf hr) z := by
    intro hzz
    have hgen : ∀ a : α, GeneratedBy op z a →
        Quotient.mk (setoidOf hr) a = Quotient.mk (setoidOf hr) z := by
      intro a ha
      induction ha with
      | base => rfl
      | @mul a b _ _ iha ihb =>
          change quotOp op hr hcompat (Quotient.mk (setoidOf hr) a)
            (Quotient.mk (setoidOf hr) b) = _
          rw [iha, ihb, hzz]
    obtain ⟨a, b, hab⟩ := hproper
    exact hab (Quotient.exact
      ((hgen a (generatedBy_of_minimal h hmin hz a)).trans
        (hgen b (generatedBy_of_minimal h hmin hz b)).symm))
  exact ⟨hcard, six_le_card_of_e255 hQ677 hQ255 hidem, by omega⟩

end ThirtyFiveEqHelpers

theorem solution
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(hmin : ∀ n : ℕ, n < Nat.card α → ∀ op' : Fin n → Fin n → Fin n,
  FiniteMagmaE677.E677 op' → FiniteMagmaE677.E255 op')
(z : α) (hz : op (op (op z z) z) z ≠ z)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hrz : r z (op (op (op z z) z) z))
(hproper : ∃ a b : α, ¬ r a b)
(h7 : ∀ op' : Fin 7 → Fin 7 → Fin 7, FiniteMagmaE677.E677 op' → ∃ x : Fin 7, op' x x = x)
(h35 : Nat.card α = 35) :
Nat.card (Quot r) = 7 ∧ Nat.card {x : α // r z x} = 5 ∧ ∃ e : α, r (op e e) e := by
  classical
  obtain ⟨hcard, hQ6, hm4⟩ := ThirtyFiveEqHelpers.card_facts h hmin hz hr hcompat hrz hproper
  obtain ⟨hQ7, hm5⟩ := ThirtyFiveEqHelpers.eq_seven_and_eq_five_of_mul_eq (hcard.symm.trans h35) hQ6 hm4
  obtain ⟨c, hc⟩ := ThirtyFiveEqHelpers.exists_idempotent_of_card (ThirtyFiveEqHelpers.e677_quotOp h hr hcompat) h7 hQ7
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective c
  exact ⟨hQ7, hm5, e, Quotient.exact (a := op e e) (b := e) hc⟩

#print axioms solution
