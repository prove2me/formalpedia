-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.lift_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:19.204796+00:00
-- url     : https://prove2.me/submissions/533dda94-89eb-4bfd-92a3-133b9a17be02

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
    lift (first - second) = lift first - lift second := by
  funext coordinate
  refine Fin.cases ?_ (fun index => ?_) coordinate
  · simp [lift, coordinateSum, Finset.sum_sub_distrib]
    ring
  · simp [lift]
end BooleanIsoperimetry.CoherentGap
