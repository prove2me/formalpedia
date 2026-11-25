-- Prove2me | solution 1 for BeckFialaMatrix.mem_floatingCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:55:23.463552+00:00
-- url     : https://prove2.me/submissions/043ad4a0-2818-458e-888c-c705bda584cc

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

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution {x : Fin N → ℚ} {i : Fin N} :
    i ∈ floatingCoordinates x ↔ 0 < x i ∧ x i < 1 := by
  simp [floatingCoordinates]
end BeckFialaMatrix
