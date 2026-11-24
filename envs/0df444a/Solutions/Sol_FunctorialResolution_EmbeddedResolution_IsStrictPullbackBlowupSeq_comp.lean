-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:24.144944+00:00
-- url     : https://prove2.me/submissions/b71930b9-ed28-4573-b44a-2867db62f19e

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
theorem _root_.solution {X'' X' X : Scheme.{u}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
    {u : SequenceOfBlowups X''} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq ψ u t) (ht : IsStrictPullbackBlowupSeq φ t s) :
    IsStrictPullbackBlowupSeq (ψ ≫ φ) u s := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := hu
  obtain ⟨hl2, τ, hz2, hp2, hc2⟩ := ht
  have hle : ∀ i : ℕ, i ≤ u.length → i ≤ t.length := fun i hi => by omega
  have hlt : ∀ i : ℕ, i < u.length → i < t.length := fun i hi => by omega
  refine ⟨hl1.trans hl2, fun i hi => σ i hi ≫ τ i (hle i hi), ?_, ?_, ?_⟩
  · rw [Category.assoc, hz2, ← Category.assoc, hz1, Category.assoc]
  · intro i hi
    exact (hp1 i hi).paste_horiz (hp2 i (hlt i hi))
  · intro i hi
    rw [hc1 i hi, hc2 i (hlt i hi)]
    simp [Scheme.IdealSheafData.comap_comp]
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
