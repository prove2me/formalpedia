-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.residual_succ_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:51.072797+00:00
-- url     : https://prove2.me/submissions/9e7a4c28-bf26-403d-ab81-edf4a7350f4d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyHeight_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (width dimension : ℕ) :
    residual (width + 1) (dimension + 1) =
      residual width dimension +
        conwayGuyDifference dimension -
          conwayGuyHeight dimension := by
  rw [residual, residual, conwayGuyHeight_succ, Fin.sum_univ_succ]
  have hargument :
      ∀ index : Fin width,
        dimension + 1 - index.succ.val - 1 =
          dimension - index.val - 1 := by
    intro index
    change dimension + 1 - (index.val + 1) - 1 =
      dimension - index.val - 1
    omega
  simp_rw [hargument]
  have hzero :
      dimension + 1 - (0 : Fin (width + 1)).val - 1 = dimension := by
    simp
  rw [hzero]
  ring
end BooleanIsoperimetry.CoherentGap
