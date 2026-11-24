-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_u_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:15.964071+00:00
-- url     : https://prove2.me/submissions/c5aea4c1-4046-44e6-bf22-105552f4e3cc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_holo_contDiffOn

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
    ContDiffOn ℂ n (fun x => fderiv ℂ g x (Pi.single k 1)) Ω := by
  have h := holo_contDiffOn hΩ hg (n + 1)
  have h' : ContDiffOn ℂ ((n : WithTop ℕ∞) + 1) g Ω := by exact_mod_cast h
  have h2 := ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp h').2.2
  exact h2.clm_apply contDiffOn_const
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
