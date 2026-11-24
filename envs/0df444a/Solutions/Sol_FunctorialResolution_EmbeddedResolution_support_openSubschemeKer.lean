-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_openSubschemeKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:31.516259+00:00
-- url     : https://prove2.me/submissions/f5d4a9df-bd3f-4ad1-9730-1675130d7724

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_openSubschemeKer_eq_ker

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
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens)
    (hW : IsClosed (W : Set Z.subscheme)) :
    ((openSubschemeKer Z W).support : Set X) = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun U _ hUc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hclosed : IsClosed (⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ hW
  have hcomp : ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base
      = ⇑Z.subschemeι.base ∘ ⇑(Scheme.Opens.ι W).base := rfl
  have hrange : Set.range ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base
      = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
    rw [hcomp, Set.range_comp, hrangeW]
  rw [openSubschemeKer_eq_ker, Scheme.Hom.support_ker]
  show closure (Set.range ⇑(Scheme.Opens.ι W ≫ Z.subschemeι).base)
      = ⇑Z.subschemeι.base '' (W : Set Z.subscheme)
  rw [hrange]
  exact hclosed.closure_eq
end FunctorialResolution.EmbeddedResolution
