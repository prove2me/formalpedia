-- Prove2me | solution 1 for Deduction.iteratedDeriv_laplace_meas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:19.022545+00:00
-- url     : https://prove2.me/submissions/4d9fd27a-95aa-4b9f-9a74-95f575315b58

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_IteratedDerivLaplace

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
theorem _root_.solution (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply Measurable.aestronglyMeasurable
  fun_prop
end Deduction
