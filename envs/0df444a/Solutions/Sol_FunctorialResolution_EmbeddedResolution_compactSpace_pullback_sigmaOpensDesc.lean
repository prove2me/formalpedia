-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.compactSpace_pullback_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:39.210302+00:00
-- url     : https://prove2.me/submissions/3d33dc2b-a595-46da-8043-85629e97e9b3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpensPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_sigmaOpens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [QuasiCompact g'] :
    CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) := by
  have : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hU
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : QuasiCompact (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  constructor
  have hcp := QuasiCompact.isCompact_preimage (f := pullback.snd g' (sigmaOpensDesc Y U))
    Set.univ isOpen_univ isCompact_univ
  simpa using hcp
end FunctorialResolution.EmbeddedResolution
