-- Prove2me | solution 1 for Deduction.mellin_Gchi_of_ne_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:12.787892+00:00
-- url     : https://prove2.me/submissions/40fab957-8f28-4f88-a21b-4c2dea7244fa

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) : s ≠ 0 ∧ s - 1 ≠ 0 := by
  constructor
  · rintro rfl
    simp at hs
    linarith
  · intro h
    rw [sub_eq_zero.mp h] at hs
    simp at hs
end Deduction
