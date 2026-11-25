-- Prove2me | solution 1 for BeckFialaMatrix.exists_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:27:17.567456+00:00
-- url     : https://prove2.me/submissions/62008219-44a7-41d6-b252-ceb274f8d75d

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
public import Theorems.Thm_BeckFialaMatrix_exists_rounding_preserving_integral

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {m N t : ℕ} (ht : 1 ≤ t)
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  obtain ⟨y, hy, -, hbd⟩ := exists_rounding_preserving_integral ht A hA hdeg x hx
  exact ⟨y, hy, hbd⟩
end BeckFialaMatrix
