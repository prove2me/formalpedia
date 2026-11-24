-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.center_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:29.500504+00:00
-- url     : https://prove2.me/submissions/469e6d61-ba42-484c-8a16-ea0c76a15c5d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_of_isPullback_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_center_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm

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
namespace IsStrictPullbackBlowupSeq
private theorem idealSheafData_eq_top_of_comap_eq_top {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [AlgebraicGeometry.Surjective f] (I : Z.IdealSheafData)
    (h : I.comap f = ⊤) : I = ⊤ := by
  refine (Scheme.IdealSheafData.support_eq_bot_iff I).mp ?_
  have hsup := Scheme.IdealSheafData.support_comap I f
  rw [h, Scheme.IdealSheafData.support_top] at hsup
  refine TopologicalSpace.Closeds.coe_eq_empty.mp (Set.eq_empty_of_forall_notMem ?_)
  intro z hz
  obtain ⟨y, hy⟩ := f.surjective z
  rw [← hy] at hz
  have h2 : y ∈ (⊥ : TopologicalSpace.Closeds ↥Y) := by
    rw [hsup]
    exact hz
  exact h2
end IsStrictPullbackBlowupSeq
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g]
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i < s.length) :
    t.center i = ⊤ ↔ s.center i = ⊤ := by
  refine ⟨?_, fun hs => center_eq_top h i hi hs⟩
  intro ht
  obtain ⟨hlen, σ, hzero, hpb, hcen⟩ := h
  have hi' : i < t.length := by omega
  have hsurj : AlgebraicGeometry.Surjective (σ i hi'.le) :=
    surjective_of_isPullback_blowupMorphism g t s t.length σ hzero hpb i hi'.le
  have hc := hcen i hi'
  rw [ht] at hc
  exact idealSheafData_eq_top_of_comap_eq_top (σ i hi'.le) (s.center i) hc.symm
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
