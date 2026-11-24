-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.isPullbackSequenceOfBlowups_withoutIsoBlowups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:14.714577+00:00
-- url     : https://prove2.me/submissions/496b3e6b-dd2d-4208-842c-05e578a36336

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_projectionToBase
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_exists_nontrivialIndex_eq_of_center_ne_top
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_support_nonempty_iff_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_center_nontrivialIndex_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_pullbackTransitionMap_fst
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_pullbackTransitionMap_snd
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projectionToBase_of_isPullback_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_transitionMap_of_isPullback_blowupMorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt


section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem support_nonempty_iff_ne_top {A : Scheme.{u}} (I : A.IdealSheafData) :
    (∃ x, x ∈ I.support) ↔ I ≠ ⊤ := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    rw [Scheme.IdealSheafData.support_top] at hx
    exact hx
  · intro hne
    by_contra hc
    push Not at hc
    exact hne ((Scheme.IdealSheafData.support_eq_bot_iff I).mp
      (SetLike.ext fun x => iff_of_false (hc x) (fun hmem => hmem)))
private theorem comap_isoHom_eq_top_iff {A B : Scheme.{u}} (e : A ≅ B) (J : B.IdealSheafData) :
    J.comap e.hom = ⊤ ↔ J = ⊤ := by
  constructor
  · intro hJ
    have h1 : (J.comap e.hom).comap e.inv = J := by
      rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
    rw [← h1, hJ]
    simp
  · rintro rfl
    simp
namespace SequenceOfBlowups
variable {X : Scheme.{u}}
end SequenceOfBlowups
namespace IsStrictPullbackBlowupSeq
end IsStrictPullbackBlowupSeq
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ t s) :
    IsPullbackBlowupSequence φ t.withoutIsoBlowups s := by
  obtain ⟨hlen, σ, hzero, hstep, hcen⟩ := h
  have hstructPB : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) φ :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism φ t s t.length σ hzero hstep
  have hdownPB : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ t.length),
      IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) (σ a (hab.trans hb)) :=
    isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
  obtain ⟨e, he1, he2⟩ :
      ∃ e : ∀ i : ℕ, i ≤ t.withoutIsoBlowups.length →
          (t.withoutIsoBlowups.schemeAt i ≅ Limits.pullback φ (s.projectionToBase (t.nontrivialIndex i))),
        (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ Limits.pullback.fst φ (s.projectionToBase (t.nontrivialIndex i))
              = t.projectionToBase (t.nontrivialIndex i)) ∧
        (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ Limits.pullback.snd φ (s.projectionToBase (t.nontrivialIndex i))
              = σ (t.nontrivialIndex i)
                  (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))) := by
    refine ⟨fun i hi => ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback, ?_, ?_⟩
    · intro i hi
      exact ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_fst
    · intro i hi
      exact ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_snd
  refine ⟨t.nontrivialIndex, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := t.nontrivialIndex_lt_length hi
    omega
  · intro i j _ hij
    exact t.nontrivialIndex_strictMono hij
  · exact t.nontrivialIndex_lengthWithoutIsoBlowups.trans hlen
  · intro i hi
    have hi' : i < t.length := by omega
    have hcomap : ((s.center i).comap (Limits.pullback.snd φ (s.projectionToBase i))).comap
        (((hstructPB i hi'.le).flip).isoPullback.hom) = t.center i := by
      rw [← Scheme.IdealSheafData.comap_comp,
        ((hstructPB i hi'.le).flip).isoPullback_hom_snd]
      exact (hcen i hi').symm
    rw [support_nonempty_iff_ne_top]
    constructor
    · intro hne
      refine t.exists_nontrivialIndex_eq_of_center_ne_top hi' ?_
      intro htop
      exact hne ((comap_isoHom_eq_top_iff _ _).mp (hcomap.trans htop))
    · rintro ⟨j, hj, rfl⟩
      intro htop
      refine t.center_nontrivialIndex_ne_top hj ?_
      rw [← hcomap, htop]
      simp
  · intro i hi
    rw [he1 i hi, t.withoutIsoBlowups_projectionToBase]
  · intro i hi hr
    have hbi : t.nontrivialIndex (i + 1) ≤ t.length :=
      t.nontrivialIndex_le_length (show i + 1 ≤ t.lengthWithoutIsoBlowups from hi)
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Category.assoc, he1, s.pullbackTransitionMap_fst, he1, t.withoutIsoBlowups_blowupMorphism i]
      exact t.transitionMap_comp_projectionToBase (t.nontrivialIndex_monotone (Nat.le_succ i))
    · rw [Category.assoc, Category.assoc, he2, s.pullbackTransitionMap_snd, ← Category.assoc, he2,
        t.withoutIsoBlowups_blowupMorphism i]
      exact (hdownPB (t.nontrivialIndex i) (t.nontrivialIndex (i + 1))
        (t.nontrivialIndex_monotone (Nat.le_succ i)) hbi).w.symm
  · intro i hi
    rw [he2 i hi.le]
    exact hcen (t.nontrivialIndex i) (t.nontrivialIndex_lt_length hi)
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
