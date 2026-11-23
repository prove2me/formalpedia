-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:59.327844+00:00
-- url     : https://prove2.me/submissions/2ef60f4e-4aa7-4260-9926-5835debcb50c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_smooth_cutoff_eq_zero_of_two_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_lt_two_mul_of_sq_div_lt

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
theorem _root_.solution {s : ℕ} {τ : ℝ} {Z : Mat s} (hτ : 0 < τ) (h : 2 * τ ≤ ‖Z‖) : cutM τ Z = 0 := by
  by_contra hne
  have h1 : ∀ i j, ‖Z i j‖ < 2 * τ := by
    intro i j
    refine lt_two_mul_of_sq_div_lt (norm_nonneg _) hτ ?_
    by_contra hge
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_univ j) (smooth_cutoff_eq_zero_of_two_le (not_lt.mp hge))))
  have h2 : ‖Z‖ < 2 * τ :=
    (pi_norm_lt_iff (by positivity)).mpr fun i => (pi_norm_lt_iff (by positivity)).mpr (h1 i)
  exact absurd h (not_le.mpr h2)
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
