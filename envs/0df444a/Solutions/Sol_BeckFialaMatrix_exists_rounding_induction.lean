-- Prove2me | solution 1 for BeckFialaMatrix.exists_rounding_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:11:51.645122+00:00
-- url     : https://prove2.me/submissions/6b750c66-2049-489a-b943-92bbd160afb5

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_BeckFialaMatrix_Basic
public import Theorems.Thm_BeckFialaMatrix_mem_floatingCoordinates
public import Theorems.Thm_BeckFialaMatrix_eq_zero_or_one_of_not_floating
public import Theorems.Thm_BeckFialaMatrix_slack_row_bound
public import Theorems.Thm_BeckFialaMatrix_exists_rounding_step
public import Theorems.Thm_BeckFialaMatrix_exists_round_all_slack

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) :
    ∀ n : ℕ, ∀ x : Fin N → ℚ, (floatingCoordinates x).card ≤ n → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
        (∀ i ∉ floatingCoordinates x, (y i : ℚ) = x i) ∧
        ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  intro n
  induction n with
  | zero =>
      intro x hcard hx
      refine exists_round_all_slack ht A hA x hx (fun j => ?_)
      have : floatingDegree A x j ≤ (floatingCoordinates x).card :=
        card_le_card (filter_subset _ _)
      omega
  | succ n ih =>
      intro x hcard hx
      by_cases hall : ∀ j, floatingDegree A x j ≤ t
      · exact exists_round_all_slack ht A hA x hx hall
      · push Not at hall
        obtain ⟨j0, hj0⟩ := hall
        obtain ⟨x', hx', hfix, hlt, htight⟩ :=
          exists_rounding_step A hdeg x hx j0 hj0
        obtain ⟨y, hy01, hagree', hbd'⟩ := ih x' (by omega) hx'
        have hagree : ∀ i ∉ floatingCoordinates x, (y i : ℚ) = x i := by
          intro i hi
          have hxx : x' i = x i := hfix i hi
          have : i ∉ floatingCoordinates x' := by
            rw [mem_floatingCoordinates, hxx]
            rcases eq_zero_or_one_of_not_floating (hx i) hi with h | h <;> simp [h]
          rw [hagree' i this, hxx]
        refine ⟨y, hy01, hagree, fun j => ?_⟩
        by_cases hs : floatingDegree A x j ≤ t
        · exact slack_row_bound ht A hA x y hy01 hagree j hs
        · push Not at hs
          have hsum : ∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)
              = ∑ i, (A j i : ℚ) * ((y i : ℚ) - x' i) := by
            have h1 : ∀ z : Fin N → ℚ, ∑ i, (A j i : ℚ) * ((y i : ℚ) - z i)
                = (∑ i, (A j i : ℚ) * (y i : ℚ)) - ∑ i, (A j i : ℚ) * z i := by
              intro z
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [h1, h1, htight j hs]
          rw [hsum]
          exact hbd' j
end BeckFialaMatrix
