-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_nsq_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:07.522805+00:00
-- url     : https://prove2.me/submissions/66bc5338-b742-4c8d-9528-0f390cc865b5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_u_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_cu_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_nsq_eq

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
theorem _root_.solution {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (k : Fin d) (n : ℕ) :
    ContDiffOn ℝ n (fun x => Complex.normSq (fderiv ℂ g x (Pi.single k 1))) Ω := by
  simp only [bkb_nsq_eq]
  exact Complex.reCLM.contDiff.comp_contDiffOn
    ((bkb_cu_contDiffOn hΩ hg k n).smul ((bkb_u_contDiffOn hΩ hg k n).restrict_scalars ℝ))
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
