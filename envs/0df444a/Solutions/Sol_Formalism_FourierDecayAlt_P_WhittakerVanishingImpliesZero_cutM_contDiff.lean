-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:58.85188+00:00
-- url     : https://prove2.me/submissions/8e517475-407b-49e2-9141-f3c877c46eaf

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_contDiff_smooth_cutoff

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
theorem _root_.solution {s : ℕ} (τ : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutM (s := s) τ) := by
  show ContDiff ℝ n (fun Z : Mat s => ∏ i, ∏ j, chi0 (‖Z i j‖ ^ 2 / τ ^ 2))
  refine contDiff_prod fun i _ => contDiff_prod fun j _ => contDiff_smooth_cutoff.comp ?_
  exact ((contDiff_apply_apply ℝ ℂ i j).norm_sq ℝ).div_const _
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
