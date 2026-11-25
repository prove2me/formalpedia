-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_isomorphic_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:46.259419+00:00
-- url     : https://prove2.me/submissions/eab977bd-8f6c-4940-abfb-ba16b4d07bfe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans


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
    {t : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : s.Isomorphic s') :
    IsStrictPullbackBlowupSeq g t s' := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := h
  obtain ⟨hl2, e, hz2, hp2, hc2⟩ := he
  have hle : ∀ i : ℕ, i ≤ t.length → i ≤ s.length := fun i hi => by omega
  have hlt : ∀ i : ℕ, i < t.length → i < s.length := fun i hi => by omega
  refine ⟨hl1.trans hl2, fun i hi => σ i hi ≫ (e i (hle i hi)).hom, ?_, ?_, ?_⟩
  · rw [Category.assoc, hz2]
    exact hz1
  · intro i hi
    refine (hp1 i hi).paste_horiz ?_
    exact IsPullback.of_horiz_isIso ⟨hp2 i (hlt i hi)⟩
  · intro i hi
    have h2 := hc2 i (hlt i hi)
    rw [hc1 i hi, ← h2]
    simp [Scheme.IdealSheafData.comap_comp]
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
