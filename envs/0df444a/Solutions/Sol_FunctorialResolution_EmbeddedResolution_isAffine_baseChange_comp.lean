-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isAffine_baseChange_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:09.012242+00:00
-- url     : https://prove2.me/submissions/1a7d8c45-fafc-468b-9183-573ce895ee32

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange (c ≫ f) K) :=
  isAffine_baseChange (c ≫ f) K
end FunctorialResolution.EmbeddedResolution
