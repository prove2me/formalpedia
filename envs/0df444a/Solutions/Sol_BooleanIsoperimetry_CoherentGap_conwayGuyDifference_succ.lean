-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.conwayGuyDifference_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:30.384341+00:00
-- url     : https://prove2.me/submissions/8ab61e85-b936-4465-bd25-dce94c79b3b7

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (index : ℕ) :
    conwayGuyDifference (index + 1) =
      ∑ offset ∈ Finset.range (guide (index + 2)),
        conwayGuyDifference (index - offset) := by
  simp [conwayGuyDifference, difference]
end BooleanIsoperimetry.CoherentGap
