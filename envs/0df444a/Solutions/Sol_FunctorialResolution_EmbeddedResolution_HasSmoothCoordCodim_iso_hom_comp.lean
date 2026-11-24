-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.iso_hom_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:39.168194+00:00
-- url     : https://prove2.me/submissions/a094dca0-a4f0-48cf-ad6f-f3359152dc39

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimensionPullback
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
theorem _root_.solution {X X' X₀ : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (e : X₀ ≅ X) :
    HasSmoothCoordCodim s (e.hom ≫ τ) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h (e.hom.base x)
  refine ⟨U, hU, q, hq, hqs, ?_⟩
  rw [restrictIdeal_eq_comap_ι, Scheme.Hom.ker_comp_of_isIso, ← restrictIdeal_eq_comap_ι, hker]
end FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
