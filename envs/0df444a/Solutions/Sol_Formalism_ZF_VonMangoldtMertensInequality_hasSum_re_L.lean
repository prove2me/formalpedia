-- Prove2me | solution 1 for Formalism.ZF.VonMangoldtMertensInequality.hasSum_re_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:09.784272+00:00
-- url     : https://prove2.me/submissions/ae3d70fd-4e32-4b10-a71e-95b348849552

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ThreeFourOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.VonMangoldtMertensInequality
namespace Formalism.ZF.VonMangoldtMertensInequality
theorem _root_.solution {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun n => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re)
      (-(deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I))).re := by
  have hs : 1 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div] at h1
  simpa only [Complex.reCLM_apply] using Complex.reCLM.hasSum h1
end Formalism.ZF.VonMangoldtMertensInequality
