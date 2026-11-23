-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:59.31184+00:00
-- url     : https://prove2.me/submissions/a342b6c1-dd9d-4380-b983-8891228f8eaf

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
theorem _root_.solution {d : ℕ} (δ : ℝ) (z : ℂ) {n : ℕ∞} : ContDiff ℝ n (critCut (n := d) δ z) := by
  show ContDiff ℝ n (fun x : Fin d → ℂ => ∏ k, chi0 (‖x k - z‖ ^ 2 / δ ^ 2))
  refine contDiff_prod fun k _ => contDiff_smooth_cutoff.comp ?_
  exact (((contDiff_apply ℝ ℂ k).sub contDiff_const).norm_sq ℝ).div_const _
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
