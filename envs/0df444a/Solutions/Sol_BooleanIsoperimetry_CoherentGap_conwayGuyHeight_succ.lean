-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.conwayGuyHeight_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:01.672122+00:00
-- url     : https://prove2.me/submissions/aa5e7478-a196-49ea-8b5a-e20b86d6704f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (dimension : ℕ) :
    conwayGuyHeight (dimension + 1) =
      conwayGuyHeight dimension + conwayGuyDifference dimension := by
  simp [conwayGuyHeight, Finset.sum_range_succ]
end BooleanIsoperimetry.CoherentGap
