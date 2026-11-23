-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.continuousOn_g2_symmetric_interval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:45.387783+00:00
-- url     : https://prove2.me/submissions/44be1d88-1382-4951-b767-b28f47831fcd

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {a : ℝ} (ha : a < 1) (ha0 : 0 ≤ a) : ContinuousOn g2 (uIcc (-a) a) := by
  apply ContinuousOn.div continuousOn_const
  · exact ((continuous_const.sub (continuous_id.pow 2)).mul
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))).continuousOn
  · intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    have hp : 0 < 1 - x ^ 2 := by linarith
    exact (mul_pos hp (Real.sqrt_pos.2 hp)).ne'
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
