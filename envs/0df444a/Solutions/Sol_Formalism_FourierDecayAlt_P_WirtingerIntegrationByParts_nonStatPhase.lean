-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.nonStatPhase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:37.756351+00:00
-- url     : https://prove2.me/submissions/5f2b7aca-6c97-422d-ad67-8faae298403d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_main_induction

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
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution : NonStatPhase := by
  intro d q β hβ
  obtain ⟨B, hB, hBk⟩ := bk_bound d q
  refine ⟨(2 / ‖β‖ * d * (2 ^ q * B)) ^ q, ?_⟩
  intro Ω g η P S hΩ hg hη hP hlow hder V _ _ _ a ha hc hsupp hb t ht
  have hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, norm_zero] at this
    linarith
  exact main_induction hβ ht hΩ hg hη hP hlow hB
    (fun x hx k => hBk Ω g P hΩ hg hP hne x hx (hder x hx) k) q le_rfl S a ha hc hsupp hb
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
