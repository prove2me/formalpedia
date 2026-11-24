-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isIso_restrict_lastStructMap_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:28:47.815365+00:00
-- url     : https://prove2.me/submissions/c460887a-49df-446c-be41-4b2f4db6954f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_IsoAwayFromCenters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIso_restrict_lastStructMap_of_centersLieOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (s : SequenceOfBlowups X)
    (hs : s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  refine isIso_restrict_lastStructMap_of_centersLieOver s _ f.smoothLocus ?_ hs
  show Disjoint (f.smoothLocus : Set X) ((f.smoothLocus : Set X)ᶜ)
  exact disjoint_compl_right
end FunctorialResolution.EmbeddedResolution
