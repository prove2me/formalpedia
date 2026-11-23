-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.norm_V
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:54.496583+00:00
-- url     : https://prove2.me/submissions/7ed7d245-51d2-41fb-b7b1-cd485eeca45f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_ee_norm

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
theorem _root_.solution {u : ℝ} (hu : 0 < u) (t : ℝ) : ‖ee u t / (Complex.I * u)‖ = 1 / u := by
  rw [norm_div, ee_norm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
