-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.center_ne_top_of_forall_center_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:35.556872+00:00
-- url     : https://prove2.me/submissions/3684eb4a-1c20-4292-993e-48acb4455bec

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition

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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s)
    (ht : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨hlen, _, _, _, hcen⟩ := h
  intro i hi htop
  have hi' : i < t.length := by omega
  refine ht i hi' ?_
  rw [hcen i hi', htop]
  simp
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
