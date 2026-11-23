-- Prove2me | solution 1 for Deduction.landau_tails_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:20.092802+00:00
-- url     : https://prove2.me/submissions/cc08f7e0-7f2f-49b4-b5fc-34da49d521fa

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_kernelIntegral
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauTails
import Theorems.Thm_Deduction_kernel_integral


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
theorem _root_.solution (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) := by
  by_contra h
  have h1 := kernel_integral k a ha
  rw [integral_undef h] at h1
  have : 0 < (a ^ (k + 1))⁻¹ := by positivity
  linarith
end Deduction
