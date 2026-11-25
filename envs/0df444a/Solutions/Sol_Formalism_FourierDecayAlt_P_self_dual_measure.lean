-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.self_dual_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:05.834815+00:00
-- url     : https://prove2.me/submissions/c8ecc903-e32a-4b7d-93bb-4eb50c49c031

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_double_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SelfDual := by
  intro β hβ f w
  unfold mu
  rw [double_smul β hβ]
  have hc : 0 < ‖β‖ / (2 * Real.pi) := by
    have := norm_pos_iff.mpr hβ
    positivity
  rw [Real.coe_toNNReal _ hc.le, mul_inv_cancel₀ (by positivity)]
  simp
end Formalism.FourierDecayAlt.P
