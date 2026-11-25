-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.comp_isStrictPullbackSequenceOfBlowups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:51.488321+00:00
-- url     : https://prove2.me/submissions/396f5c29-71cd-4dcf-bce3-7fb04bfb6c0a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StrictPullbackComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_pullbackTransitionMap_fst
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_pullbackTransitionMap_snd
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projectionToBase_of_isPullback_blowupMorphism

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
private theorem mem_support_comap {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData)
    (x : ↥A) : x ∈ (I.comap f).support ↔ f.base x ∈ I.support := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
  exact Iff.rfl
private theorem support_comap_pullback_snd_nonempty_iff {W V Y T : Scheme.{u}} (u : V ⟶ Y) (c : W ⟶ V)
    [AlgebraicGeometry.Surjective c] (g : T ⟶ Y) (I : T.IdealSheafData) :
    (∃ x, x ∈ (I.comap (Limits.pullback.snd (c ≫ u) g)).support) ↔
      (∃ x, x ∈ (I.comap (Limits.pullback.snd u g)).support) := by
  obtain ⟨q, hq1, hq2⟩ :
      ∃ q : Limits.pullback (c ≫ u) g ⟶ Limits.pullback u g,
        q ≫ Limits.pullback.fst u g = Limits.pullback.fst (c ≫ u) g ≫ c ∧
          q ≫ Limits.pullback.snd u g = Limits.pullback.snd (c ≫ u) g :=
    ⟨Limits.pullback.lift (Limits.pullback.fst (c ≫ u) g ≫ c)
        (Limits.pullback.snd (c ≫ u) g)
        (by rw [Category.assoc]; exact Limits.pullback.condition),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  have hA : IsPullback (Limits.pullback.fst (c ≫ u) g) q c (Limits.pullback.fst u g) := by
    refine IsPullback.of_bot ?_ hq1.symm (IsPullback.of_hasPullback u g)
    rw [hq2]
    exact IsPullback.of_hasPullback (c ≫ u) g
  have hqs : AlgebraicGeometry.Surjective q := by
    rw [← hA.isoPullback_hom_snd]
    infer_instance
  have hbase : ∀ x : ↥(Limits.pullback (c ≫ u) g),
      (Limits.pullback.snd (c ≫ u) g).base x =
        (Limits.pullback.snd u g).base (q.base x) := by
    intro x
    rw [← hq2]
    simp
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_support_comap] at hx
    refine ⟨q.base x, ?_⟩
    rw [mem_support_comap, ← hbase x]
    exact hx
  · rintro ⟨y, hy⟩
    rw [mem_support_comap] at hy
    obtain ⟨x, hx⟩ := hqs.surj y
    refine ⟨x, ?_⟩
    rw [mem_support_comap, hbase x, hx]
    exact hy
namespace IsPullbackBlowupSequence
end IsPullbackBlowupSequence
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
namespace FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
theorem _root_.solution {W V Y : Scheme.{u}} {u : V ⟶ Y} {c : W ⟶ V}
    [AlgebraicGeometry.Surjective c]
    {s : SequenceOfBlowups Y} {s' : SequenceOfBlowups V} {t : SequenceOfBlowups W}
    (h : IsPullbackBlowupSequence u s' s) (hc : IsStrictPullbackBlowupSeq c t s') :
    IsPullbackBlowupSequence (c ≫ u) t s := by
  unfold FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence at h ⊢
  unfold FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq at hc
  obtain ⟨r, e, hr1, hr2, hr3, hr4, hefst, hestep, hecenter⟩ := h
  obtain ⟨hlen, σ, hzero, hstep, hcenter⟩ := hc
  have hle : ∀ i : ℕ, i ≤ t.length → i ≤ s'.length := by
    intro i hi
    omega
  have hsq : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (σ i hi) (t.projectionToBase i) (s'.projectionToBase i) c :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism c t s' t.length σ hzero hstep
  have hpaste : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (t.projectionToBase i)
        (σ i hi ≫ (e i (hle i hi)).hom ≫ Limits.pullback.snd u (s.projectionToBase (r i)))
        (c ≫ u) (s.projectionToBase (r i)) := by
    intro i hi
    have hcomm : s'.projectionToBase i ≫ u =
        ((e i (hle i hi)).hom ≫ Limits.pullback.snd u (s.projectionToBase (r i))) ≫
          s.projectionToBase (r i) := by
      rw [← hefst i (hle i hi), Category.assoc, Category.assoc, Limits.pullback.condition]
    exact (hsq i hi).flip.paste_vert
      (IsPullback.of_iso_pullback ⟨hcomm⟩ (e i (hle i hi)) (hefst i (hle i hi)) rfl)
  have hFfst : ∀ (i : ℕ) (hi : i ≤ t.length),
      ((hpaste i hi).isoPullback).hom ≫
          Limits.pullback.fst (c ≫ u) (s.projectionToBase (r i)) = t.projectionToBase i :=
    fun i hi => (hpaste i hi).isoPullback_hom_fst
  have hFsnd : ∀ (i : ℕ) (hi : i ≤ t.length),
      ((hpaste i hi).isoPullback).hom ≫
          Limits.pullback.snd (c ≫ u) (s.projectionToBase (r i)) =
        σ i hi ≫ (e i (hle i hi)).hom ≫ Limits.pullback.snd u (s.projectionToBase (r i)) :=
    fun i hi => (hpaste i hi).isoPullback_hom_snd
  have hFsnd' : ∀ (i : ℕ) (hi : i ≤ t.length) {Z : Scheme.{u}} (k : s.schemeAt (r i) ⟶ Z),
      ((hpaste i hi).isoPullback).hom ≫
          Limits.pullback.snd (c ≫ u) (s.projectionToBase (r i)) ≫ k =
        σ i hi ≫ (e i (hle i hi)).hom ≫
          Limits.pullback.snd u (s.projectionToBase (r i)) ≫ k := by
    intro i hi Z k
    rw [← Category.assoc, hFsnd, Category.assoc, Category.assoc]
  have hc1 : ∀ i < t.length, r i < s.length := by
    intro i hi
    exact hr1 i (by omega)
  have hc2 : ∀ (i j : ℕ), j ≤ t.length → i < j → r i < r j := by
    intro i j hj hij
    exact hr2 i j (by omega) hij
  have hc3 : r t.length = s.length := by
    rw [hlen]
    exact hr3
  have hc4 : ∀ i < s.length,
      (∃ x, x ∈ ((s.center i).comap
        (Limits.pullback.snd (c ≫ u) (s.projectionToBase i))).support) ↔
        ∃ j < t.length, r j = i := by
    intro i hi
    refine (support_comap_pullback_snd_nonempty_iff u c (s.projectionToBase i) (s.center i)).trans ?_
    refine (hr4 i hi).trans ?_
    constructor
    · rintro ⟨j, hj, hji⟩
      exact ⟨j, by omega, hji⟩
    · rintro ⟨j, hj, hji⟩
      exact ⟨j, by omega, hji⟩
  have hc6 : ∀ (i : ℕ) (hi : i < t.length) (hrr : r i ≤ r (i + 1)),
      t.transitionMapSucc i ≫ ((hpaste i (Nat.le_of_lt hi)).isoPullback).hom =
        ((hpaste (i + 1) hi).isoPullback).hom ≫ s.pullbackTransitionMap (c ≫ u) hrr := by
    intro i hi hrr
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hFfst]
      rw [t.blowupMorphism_eq_transitionMap]
      exact t.transitionMap_comp_projectionToBase _
    · simp only [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_snd, hFsnd, hFsnd']
      rw [← Category.assoc, ← (hstep i hi).w, Category.assoc,
        ← Category.assoc (s'.transitionMapSucc i), hestep i (by omega) hrr, Category.assoc,
        SequenceOfBlowups.pullbackTransitionMap_snd]
  have hc7 : ∀ (i : ℕ) (hi : i < t.length),
      t.center i = (s.center (r i)).comap
        (((hpaste i (Nat.le_of_lt hi)).isoPullback).hom ≫
          Limits.pullback.snd (c ≫ u) (s.projectionToBase (r i))) := by
    intro i hi
    rw [hcenter i hi, hecenter i (by omega), hFsnd,
      ← Scheme.IdealSheafData.comap_comp]
  exact ⟨r, fun i hi => (hpaste i hi).isoPullback, hc1, hc2, hc3, hc4, hFfst, hc6, hc7⟩
end FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
