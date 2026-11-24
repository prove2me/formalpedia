-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:24.528796+00:00
-- url     : https://prove2.me/submissions/e340ad63-a5bc-4325-a9fa-d8a1e42dadfe

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_one_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_common_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution (s k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ j ≤ k, ∀ Z : Mat s,
    ‖iteratedFDeriv ℝ j (cutM τ) Z‖ ≤ C * (τ ^ j)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := common_bound k (fun j (Z : Mat s) => ‖iteratedFDeriv ℝ j (cutM 1) Z‖)
    (cutM_one_bound s)
  refine ⟨C, hC0, fun τ hτ j hj Z => ?_⟩
  rw [cutM_scale hτ, iteratedFDeriv_comp_const_smul τ⁻¹ (cutM_contDiff 1 (n := j)), norm_smul, norm_pow,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ), inv_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC j hj _) (by positivity)
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
