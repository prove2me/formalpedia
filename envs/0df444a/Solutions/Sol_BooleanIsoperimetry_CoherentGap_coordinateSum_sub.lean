-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.coordinateSum_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:16.979762+00:00
-- url     : https://prove2.me/submissions/7001482a-191e-45a8-a528-a6063df1f70d

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
theorem _root_.solution {n : ℕ} (first second : Relation n) :
    coordinateSum (first - second) =
      coordinateSum first - coordinateSum second := by
  simp [coordinateSum, Finset.sum_sub_distrib]
end BooleanIsoperimetry.CoherentGap
