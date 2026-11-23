-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:30.33103+00:00
-- url     : https://prove2.me/submissions/9ad5b17d-a604-472d-b2b1-fa7edb2bdb8b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

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
    (hg : DifferentiableOn ℂ g Ω) (x v : Fin d → ℂ) (ζ : ℂ) (h : x + ζ • v ∈ Ω) :
    HasDerivAt (fun ζ : ℂ => g (x + ζ • v)) (fderiv ℂ g (x + ζ • v) v) ζ := by
  have h1 : HasFDerivAt g (fderiv ℂ g (x + ζ • v)) (x + ζ • v) :=
    (hg.differentiableAt (hΩ.mem_nhds h)).hasFDerivAt
  have h2 : HasDerivAt (fun ζ : ℂ => x + ζ • v) v ζ := by
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add x
  exact h1.comp_hasDerivAt ζ h2
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
