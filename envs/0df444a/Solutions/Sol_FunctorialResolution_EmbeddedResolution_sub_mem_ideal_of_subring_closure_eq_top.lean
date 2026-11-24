-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sub_mem_ideal_of_subring_closure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:09.251635+00:00
-- url     : https://prove2.me/submissions/ca8d16fb-6ace-490e-a9d4-cf5fddf76de8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {B A : Type u} [CommRing B] [CommRing A]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f g : B →+* A) (J : Ideal A) (S : Set B)
    (hS : Subring.closure S = ⊤) (hmem : ∀ b ∈ S, f b - g b ∈ J) (b : B) :
    f b - g b ∈ J := by
  have hsub : Subring.closure S ≤ eqModIdealSubring f g J :=
    Subring.closure_le.mpr (fun x hx => hmem x hx)
  rw [hS] at hsub
  exact hsub (Subring.mem_top b)
end FunctorialResolution.EmbeddedResolution
