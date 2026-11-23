-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleThresholdsOne_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:47.237303+00:00
-- url     : https://prove2.me/submissions/f28b27be-704d-4d2c-af2e-9083438dc45f

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
theorem _root_.solution : ScaleThresholdsOne := by
  intro ka sb TT r hka hTT
  have k3 : (ka ^ (4 * r)) ^ (-(1 / 2 : ℝ)) = (ka ^ (2 * r))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, show 4 * r = 2 * r * 2 by ring, pow_mul,
      Real.sqrt_sq (by positivity)]
  have hk2 : ka ^ (2 * r) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [zpow_neg_one]
    field_simp
  · rw [Real.mul_rpow (by positivity) hTT.le, k3]
    field_simp
end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
