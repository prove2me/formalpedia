-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:57.384966+00:00
-- url     : https://prove2.me/submissions/62a8425b-d35c-4c04-9ea2-0d732e9c44a5

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.ThresholdBelow := by
  intro m i s C c c₂ κ N I A hκ hN hI hA hc hc₂ h4 h2
  unfold Formalism.FourierDecayAlt.Sz.lamThreshold
  have hW : 0 ≤ (κ ^ (m - 1))⁻¹ * A := mul_nonneg (inv_nonneg.mpr (pow_nonneg hκ.le _)) hA
  have hb : 4 * κ / (I / (c * N)) = 4 * c * (κ * N / I) := by
    rw [div_div_eq_mul_div]
    ring
  have hb0 : 0 ≤ 4 * κ / (I / (c * N)) := by positivity
  have hbase : 4 * κ / (I / (c * N)) ≤ C * κ * N / I := by
    rw [hb, show C * κ * N / I = C * (κ * N / I) by ring]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hpow := pow_le_pow_left₀ hb0 hbase (2 * (i - 1) + s - 1)
  have hfront : (1 / 2) * (c₂ * ((κ ^ (m - 1))⁻¹ * A)) ≤ C * ((κ ^ (m - 1))⁻¹ * A) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hW
  exact mul_le_mul hfront hpow (pow_nonneg hb0 _) (mul_nonneg (by linarith) hW)
end Formalism.FourierDecayAlt.P
