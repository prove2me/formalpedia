-- Prove2me | solution 1 for FiniteMagmaE677.e255_of_congruence_classes_card_three
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T22:42:54.525067+00:00
-- url     : https://prove2.me/submissions/448eb026-da5d-4eb5-8ffa-9739a644b758

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib

/-!
# Congruences with three-element classes lift `E255`

Let `op` be a finite `E677` magma and `r` a congruence of `op` all of whose classes have
three elements.  If `E255` holds modulo `r`, then `E255` holds.

## Proof

Let `r (s ◇ b) b`, and write `X`, `V`, `U` for the classes of `b`, `s` and `b ◇ s`.
`E677` at `(b, s)` and left cancellation modulo `r` give `r (b ◇ (b ◇ s)) b`, so left
translations map `V × X → X`, `X × V → U` and `X × U → X`, each row injectively.  Put
`σ_v = L_v` on `X`, `D_a = L_a` on `V` and `E_x = L_x` on `U`.  `E677` at `(x, v)` with
`x ∈ X` and `v ∈ V` reads `σ_v (E_x (D_{σ_v x} v)) = x` (★).

* `exists_common_preimage_of_no_fixed_point`: if three-element sets carry injective rows
  `σ`, `D`, `E` satisfying (★), and no `σ_v` fixes the point `t`, then some `v₀`
  satisfies `E_y (D_x v₀) = x` for all `x` and `y`.  The proof moves `X`, `V`, `U` to
  `Fin 3`, with `t ↦ 0` and `E_t` the identity, and checks the finite statement by
  `decide +kernel`.
* `exists_fixer_of_card_class_eq_three`: if no element of `V` fixes `b`, the previous
  item gives `v₀`, and `E677` at `(x, y)` with two left cancellations gives
  `(y ◇ x) ◇ y = v₀` for all `x, y ∈ X`.  For `c ∈ X` with `c ≠ b`, some `x ∈ X` has
  `c ◇ x = b ◇ b`, so `(b ◇ b) ◇ c = v₀ = (b ◇ b) ◇ b` and `c = b`, a contradiction.
* `solution`: `r (((z ◇ z) ◇ z) ◇ z) z` and a fixer of `z` give `E255` at `z`.

Ported from `lean/E677/ClassThreeLift.lean` of a private repo (Adam McKenna).
-/

universe u
open FiniteMagmaE677

namespace ClassThreeHelpers

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

end Fixer

end ClassThreeHelpers

theorem solution
{α : Type u} [Finite α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
(r : α → α → Prop) (hr : Equivalence r)
(hcompat : ∀ a a' b b' : α, r a a' → r b b' → r (op a b) (op a' b'))
(hcard : ∀ a : α, Nat.card {x : α // r a x} = 3)
(hquot : ∀ x : α, r (op (op (op x x) x) x) x) :
FiniteMagmaE677.E255 op := by
  intro z
  exact ClassThreeHelpers.eq255_from_fixer_exists h z
    (ClassThreeHelpers.exists_fixer_of_card_class_eq_three h hr hcompat hcard (hquot z))

#print axioms solution
