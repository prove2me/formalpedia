-- Prove2me | solution 1 for BeckFialaMatrix.eq_zero_or_one_of_not_floating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:00:38.674183+00:00
-- url     : https://prove2.me/submissions/405feae6-d2ae-4922-98ed-38097a3b6da0

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

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {x : Fin N → ℚ} {i : Fin N}
    (hx : 0 ≤ x i ∧ x i ≤ 1) (h : i ∉ floatingCoordinates x) : x i = 0 ∨ x i = 1 := by
  rw [mem_floatingCoordinates] at h
  push Not at h
  rcases lt_or_eq_of_le hx.1 with h0 | h0
  · exact Or.inr (le_antisymm hx.2 (h h0))
  · exact Or.inl h0.symm
end BeckFialaMatrix
