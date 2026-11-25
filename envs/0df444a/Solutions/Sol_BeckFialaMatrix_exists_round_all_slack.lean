-- Prove2me | solution 1 for BeckFialaMatrix.exists_round_all_slack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:16.329037+00:00
-- url     : https://prove2.me/submissions/26d371d5-d1b0-4219-8344-7346d7770bd5

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
public import Theorems.Thm_BeckFialaMatrix_eq_zero_or_one_of_not_floating
public import Theorems.Thm_BeckFialaMatrix_slack_row_bound

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1) (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hall : ∀ j, floatingDegree A x j ≤ t) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i ∉ floatingCoordinates x, (y i : ℚ) = x i) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  classical
  refine ⟨fun i => if x i = 1 then 1 else 0, fun i => ?_, ?_, ?_⟩
  · by_cases h : x i = 1 <;> simp [h]
  · intro i hi
    rcases eq_zero_or_one_of_not_floating (hx i) hi with h | h <;> simp [h]
  · intro j
    refine slack_row_bound ht A hA x _ (fun i => ?_) (fun i hi => ?_) j (hall j)
    · by_cases h : x i = 1 <;> simp [h]
    · rcases eq_zero_or_one_of_not_floating (hx i) hi with h | h <;> simp [h]
end BeckFialaMatrix
