-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.vanishingIdeal_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:02.537839+00:00
-- url     : https://prove2.me/submissions/1a148f70-b493-40f3-8d4f-be2e4a141b49

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {Z₁ Z₂ : Closeds ↥X}
    (h : (Z₁ : Set ↥X) = (Z₂ : Set ↥X)) :
    Scheme.IdealSheafData.vanishingIdeal Z₁ = Scheme.IdealSheafData.vanishingIdeal Z₂ := by
  have hZ : Z₁ = Z₂ := SetLike.coe_injective h
  rw [hZ]
end FunctorialResolution.EmbeddedResolution
