-- Prove2me | solution 1 for Deduction.LFunctionConjugation.pole_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:05.393254+00:00
-- url     : https://prove2.me/submissions/e7b834cf-6f13-42a0-8789-d8a02dc5314d

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Theorems.Thm_P2M_Deduction_LFunctionConjugation_Gamma__conj_2d580e70eb48

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
open Deduction.LFunctionConjugation
open HurwitzZeta
namespace Deduction.LFunctionConjugation
theorem _root_.solution (s : ℂ) : 1 / ((starRingEnd ℂ) s - 1) / Gammaℝ ((starRingEnd ℂ) s)
    = (starRingEnd ℂ) (1 / (s - 1) / Gammaℝ s) := by
  rw [Gammaℝ_conj]
  simp [map_div₀]
end Deduction.LFunctionConjugation
