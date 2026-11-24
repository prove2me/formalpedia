-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_opens_notMem_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:29.976356+00:00
-- url     : https://prove2.me/submissions/48427248-a8f5-449f-93e1-d03d7ce8339d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (x : X)
    (hx : x ∉ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U := by
  have hclosed : IsClosed (⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ hW
  refine ⟨⟨(⇑Z.subschemeι.base '' (W : Set Z.subscheme))ᶜ, hclosed.isOpen_compl⟩, hx, ?_⟩
  intro w hw hmem
  exact hmem ⟨w, hw, rfl⟩
end FunctorialResolution.EmbeddedResolution
