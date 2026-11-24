-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:02.745112+00:00
-- url     : https://prove2.me/submissions/7058d709-ceb3-47b0-8085-eca0ecc839b3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projectionToBase_of_isPullback_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_self

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
private theorem transitionMap_self {X : Scheme.{u}} (u : SequenceOfBlowups X) {a : ℕ}
    (h : a ≤ a) : u.transitionMap h = 𝟙 (u.schemeAt a) := by
  have h0 : (CategoryTheory.homOfLE h).op = 𝟙 (Opposite.op a) := rfl
  rw [u.transitionMap_def, h0, CategoryTheory.Functor.map_id]
namespace IsStrictPullbackBlowupSeq
private theorem projectionToBase_zero {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    s.projectionToBase 0 = s.isoZero.hom := by
  rw [SequenceOfBlowups.projectionToBase_def, transitionMap_self s (le_refl 0), Category.id_comp]
private theorem blowupMorphism_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) (i : ℕ) :
    s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
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
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (h' : IsStrictPullbackBlowupSeq g t' s) :
    t.Isomorphic t' := by
  obtain ⟨hl, σ, hz, hp, hc⟩ := h
  obtain ⟨hl', τ, hz', hp', hc'⟩ := h'
  have hlen : t.length ≤ t'.length := le_of_eq (hl.trans hl'.symm)
  have hA : ∀ i : ℕ, ∀ hi : i ≤ t.length,
      IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hz hp
  have hB : ∀ i : ℕ, ∀ hi : i ≤ t'.length,
      IsPullback (τ i hi) (t'.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t' s t'.length τ hz' hp'
  have key : ∀ i : ℕ, ∀ hi : i ≤ t.length, ∃ e : t.schemeAt i ≅ t'.schemeAt i,
      e.hom ≫ τ i (hi.trans hlen) = σ i hi ∧ e.hom ≫ t'.projectionToBase i = t.projectionToBase i :=
    fun i hi =>
      ⟨(hA i hi).isoIsPullback _ _ (hB i (hi.trans hlen)),
        (hA i hi).isoIsPullback_hom_fst _ _ (hB i (hi.trans hlen)),
        (hA i hi).isoIsPullback_hom_snd _ _ (hB i (hi.trans hlen))⟩
  choose e he1 he2 using key
  refine ⟨hl.trans hl'.symm, e, ?_, ?_, ?_⟩
  · have h0 := he2 0 (Nat.zero_le t.length)
    rwa [projectionToBase_zero t', projectionToBase_zero t] at h0
  · intro i hi
    have hi2 : i < t'.length := lt_of_lt_of_le hi hlen
    refine (hB i (hi.le.trans hlen)).hom_ext ?_ ?_
    · have w1 : τ (i + 1) hi2 ≫ s.transitionMapSucc i = t'.transitionMapSucc i ≫ τ i hi2.le :=
        (hp' i hi2).w
      have w2 : σ (i + 1) hi ≫ s.transitionMapSucc i = t.transitionMapSucc i ≫ σ i hi.le := (hp i hi).w
      rw [Category.assoc, Category.assoc, ← w1, he1 i hi.le, ← Category.assoc,
        he1 (i + 1) hi]
      exact w2
    · rw [Category.assoc, Category.assoc, blowupMorphism_comp_projectionToBase t' i,
        he2 (i + 1) hi, he2 i hi.le, blowupMorphism_comp_projectionToBase t i]
  · intro i hi
    have hi2 : i < t'.length := lt_of_lt_of_le hi hlen
    rw [hc' i hi2, hc i hi, ← he1 i hi.le]
    simp [Scheme.IdealSheafData.comap_comp]
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
