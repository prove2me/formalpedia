-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_N_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:48.014837+00:00
-- url     : https://prove2.me/submissions/8036feb2-567b-4419-a9a8-854d9049132c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_nsq_contDiffOn

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
    (hg : DifferentiableOn ℂ g Ω) (n : ℕ) :
    ContDiffOn ℝ n (fun x => ∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1))) Ω :=
  ContDiffOn.sum fun l _ => bkb_nsq_contDiffOn hΩ hg l n
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
