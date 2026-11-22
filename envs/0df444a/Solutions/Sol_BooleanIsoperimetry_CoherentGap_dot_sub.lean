-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.dot_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:28.601052+00:00
-- url     : https://prove2.me/submissions/e5ad63a9-ae1a-4e31-a985-1d8844ca3224

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
theorem _root_.solution {n : ℕ} (first second weights : Relation n) :
    dot (first - second) weights =
      dot first weights - dot second weights := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]
end BooleanIsoperimetry.CoherentGap
