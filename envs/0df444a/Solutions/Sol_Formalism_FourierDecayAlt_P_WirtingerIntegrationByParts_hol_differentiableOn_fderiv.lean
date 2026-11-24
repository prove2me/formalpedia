-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_differentiableOn_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:53.312837+00:00
-- url     : https://prove2.me/submissions/6693e255-ff62-438f-bd43-40cd0bce8780

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_clm_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_differentiableOn_fderiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution [CompleteSpace F] {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (fderiv ℂ g) Ω := by
  have h : fderiv ℂ g = fun x => ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight
      (fderiv ℂ g x (Pi.single k 1)) := by
    funext x; exact hol_clm_decomp _
  rw [h]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ (Fin d → ℂ) F
    (ContinuousLinearMap.proj k)).differentiable.comp_differentiableOn
      (hol_differentiableOn_fderiv_apply hΩ hg _)
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
