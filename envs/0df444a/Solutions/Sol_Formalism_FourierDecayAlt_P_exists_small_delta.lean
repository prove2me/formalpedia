-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exists_small_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:56.840876+00:00
-- url     : https://prove2.me/submissions/68dd4842-3489-4757-835c-50e67941b3d3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_exists_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SmallDeltaExists := by
  intro m Kc hK h0
  obtain ⟨d, hd, hD⟩ := exists_lower hK h0
  have hm : (0 : ℝ) < 100 * ((m : ℝ) + 2) := by positivity
  refine ⟨min 1 d / (100 * ((m : ℝ) + 2)), by positivity, fun D hDK z hz => ?_⟩
  rw [mul_div_cancel₀ _ hm.ne']
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  have h1 : ‖z‖ ^ (m + 2) = ‖D‖ := by
    rw [← norm_pow, hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h2 : ‖z‖ ^ (m + 2) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hlt.1.le (by omega)
  have h3 := hD D hDK
  linarith [hlt.2]
end Formalism.FourierDecayAlt.P
