-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.triangular_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:51.172914+00:00
-- url     : https://prove2.me/submissions/ec98c674-01e1-4f9d-a160-4a148f32894e

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
theorem _root_.solution : StrictMono triangular := by
  intro first second hlt
  have hstep : triangular first < triangular (first + 1) := by
    simp only [triangular]
    omega
  exact hstep.trans_le (triangular_mono (by omega))
end BooleanIsoperimetry.CoherentGap
