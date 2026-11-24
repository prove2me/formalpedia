-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_continuousOn_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:06.655798+00:00
-- url     : https://prove2.me/submissions/d484738e-0473-4893-84d8-2a6aa65197b9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_clm_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_continuousOn_fderiv_apply

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
theorem _root_.solution {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : ContinuousOn (fderiv ℂ g) Ω := by
  have h : fderiv ℂ g = fun x => ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight
      (fderiv ℂ g x (Pi.single k 1)) := by
    funext x; exact hol_clm_decomp _
  rw [h]
  refine continuousOn_finsetSum _ fun k _ => ?_
  have hc : Continuous fun w : F => (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight w :=
    (ContinuousLinearMap.smulRightL ℂ (Fin d → ℂ) F (ContinuousLinearMap.proj k)).continuous
  exact hc.comp_continuousOn (hol_continuousOn_fderiv_apply hΩ hg _)
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
