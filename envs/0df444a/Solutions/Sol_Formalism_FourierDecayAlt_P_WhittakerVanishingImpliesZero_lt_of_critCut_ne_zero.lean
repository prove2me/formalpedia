-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.lt_of_critCut_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:59.817192+00:00
-- url     : https://prove2.me/submissions/39ea9542-f107-4484-b55d-08ea6b6ae3ba

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
theorem _root_.solution {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : critCut δ z x ≠ 0) (k : Fin n) : ‖x k - z‖ < 2 * δ := by
  refine lt_two_mul_of_sq_div_lt (norm_nonneg _) hδ ?_
  by_contra hge
  exact h (Finset.prod_eq_zero (Finset.mem_univ k) (smooth_cutoff_eq_zero_of_two_le (not_lt.mp hge)))
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
