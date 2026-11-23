-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.norm_add_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:49.093435+00:00
-- url     : https://prove2.me/submissions/87c6e342-70a0-4907-991f-b3afe8b9c09c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (x y : ℂ) (c : ℝ) (hc : 0 ≤ c) : c * ‖x + y‖ ^ 2 ≤ c * (1 + c) * ‖x‖ ^ 2 + (1 + c) * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h1
  have h3 : 0 ≤ (c * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  have h4 : c * ‖x + y‖ ^ 2 ≤ c * (‖x‖ + ‖y‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hc
  nlinarith
end Formalism.FourierDecayAlt.P.LEx1
