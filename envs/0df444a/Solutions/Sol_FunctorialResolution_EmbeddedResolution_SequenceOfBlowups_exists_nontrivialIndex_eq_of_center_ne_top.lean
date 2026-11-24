-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.exists_nontrivialIndex_eq_of_center_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:57:41.917648+00:00
-- url     : https://prove2.me/submissions/ea78b028-65b7-40d6-a634-be899fc6344f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IsoBlowupRemovalBaseChange

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
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
theorem _root_.solution (s : SequenceOfBlowups X) {i : ℕ} (hi : i < s.length)
    (h : s.center i ≠ ⊤) :
    ∃ j, j < s.lengthWithoutIsoBlowups ∧ s.nontrivialIndex j = i := by
  have hex : ∃ n, i < s.nontrivialIndex n :=
    ⟨s.lengthWithoutIsoBlowups, by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi⟩
  obtain ⟨n, hn1, hn2, hn3⟩ :
      ∃ n, i < s.nontrivialIndex n ∧ (∀ m, m < n → ¬ (i < s.nontrivialIndex m)) ∧ n ≤ s.lengthWithoutIsoBlowups :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm,
      Nat.find_le (by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi)⟩
  cases n with
  | zero => exact absurd (s.center_eq_top_of_lt_nontrivialIndex_zero hn1) h
  | succ m =>
      have hmi : s.nontrivialIndex m ≤ i := not_lt.mp (hn2 m (Nat.lt_succ_self m))
      refine ⟨m, by omega, ?_⟩
      rcases eq_or_lt_of_le hmi with heq | hlt
      · exact heq
      · exact absurd (s.center_eq_top_of_nontrivialIndex_lt hlt hn1) h
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
