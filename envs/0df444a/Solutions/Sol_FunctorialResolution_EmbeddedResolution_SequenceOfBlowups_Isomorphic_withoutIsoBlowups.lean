-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.Isomorphic.withoutIsoBlowups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:27.305968+00:00
-- url     : https://prove2.me/submissions/9928c67e-5da5-4713-b224-44e75bb58e70

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IsoBlowupRemoval
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_isomorphic
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isomorphic_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
end SequenceOfBlowups
private theorem isStrictPullbackSequenceOfBlowups_id_of_isomorphic {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : IsStrictPullbackBlowupSeq (𝟙 X) B B' := by
  unfold SequenceOfBlowups.Isomorphic at h
  unfold IsStrictPullbackBlowupSeq
  obtain ⟨hlen, e, hzero, hstep, hcen⟩ := h
  refine ⟨hlen, fun i hi => (e i hi).hom, ?_, ?_, ?_⟩
  · rw [Category.comp_id]
    exact hzero
  · intro i hi
    exact IsPullback.of_horiz_isIso ⟨hstep i hi⟩
  · intro i hi
    exact (hcen i hi).symm
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups.Isomorphic
theorem _root_.solution {X : Scheme.{u}} {t₁ t₂ : SequenceOfBlowups X}
    (h : t₁.Isomorphic t₂) : t₁.withoutIsoBlowups.Isomorphic t₂.withoutIsoBlowups :=
  ((isStrictPullbackSequenceOfBlowups_id_of_isomorphic h).withoutIsoBlowups).isomorphic
    (isStrictPullbackSequenceOfBlowups_id_of_isomorphic (SequenceOfBlowups.isomorphic_refl t₂.withoutIsoBlowups))
end SequenceOfBlowups.Isomorphic
end FunctorialResolution.EmbeddedResolution
