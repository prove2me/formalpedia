-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_omLong_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:45.780737+00:00
-- url     : https://prove2.me/submissions/7561309c-d979-4660-85c2-760bb1b2504e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_min_le_maxpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_integrable_long
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_long_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (m : ℕ) (β : ℂ) (r : ℝ) (hr : 0 < r) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (hA : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A) (hK : 0 ≤ K) (z : ℂ)
    (hz : r ≤ ‖z‖)
    (hb : ∀ v, ‖Φ (longM (m + 1 + 1) z v)‖ ≤ K * min 1 (‖longM (m + 1 + 1) z v‖ ^ (-A))) :
    ‖OmLong β (m + 1) Φ z‖ ≤ K * ∫ v : UT (m + 1 + 1) → ℂ,
      (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) ∂(muPi β (UT (m + 1 + 1))) := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_long m β r hr).const_mul K)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_smul, (additive_character_psi β _ 0).2.1, one_mul]
  refine (hb v).trans (mul_le_mul_of_nonneg_left ?_ hK)
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  calc min 1 (‖longM (m + 1 + 1) z v‖ ^ (-A)) ≤ (max 1 ‖longM (m + 1 + 1) z v‖) ^ (-A) := min_le_maxpow A _
    _ ≤ (max 1 ‖longM (m + 1 + 1) z v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by nlinarith)
        refine max_le_max le_rfl ?_
        refine le_trans ?_ (norm_long_le z v (longM (m + 1 + 1) z v) rfl)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hr.le]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
