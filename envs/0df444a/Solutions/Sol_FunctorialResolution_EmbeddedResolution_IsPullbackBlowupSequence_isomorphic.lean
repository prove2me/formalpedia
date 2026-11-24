-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:31.668035+00:00
-- url     : https://prove2.me/submissions/42801a95-d6f9-48ec-a596-5094583e5b22

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_zero

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
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem pullbackIsoOfEq_hom_fst {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (h : a = b) :
    (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.fst φ (s.projectionToBase b)
      = Limits.pullback.fst φ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]
private theorem pullbackIsoOfEq_hom_comp_pullbackTransitionMap {X X' : Scheme.{u}} (φ : X' ⟶ X)
    (s : SequenceOfBlowups X) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    (pullbackProjectionToBaseIsoOfEq φ s hb).hom ≫ s.pullbackTransitionMap φ hab'
      = s.pullbackTransitionMap φ hab ≫ (pullbackProjectionToBaseIsoOfEq φ s ha).hom := by
  subst ha
  subst hb
  have hpr : hab = hab' := rfl
  subst hpr
  simp [pullbackProjectionToBaseIsoOfEq]
private theorem comap_pullbackIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) {W : Scheme.{u}} (g : W ⟶ Limits.pullback φ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.snd φ (s.projectionToBase b))
      = (s.center a).comap (g ≫ Limits.pullback.snd φ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]
private theorem strictMono_enumeration_le {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    ∀ i, i < n → i < m → r i ≤ q i := by
  have main : ∀ k i : ℕ, i < k → i < n → i < m → r i ≤ q i := by
    intro k
    induction k with
    | zero => intro i hik; exact absurd hik (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hik hin him
      by_contra hcon
      push Not at hcon
      have hqL : q i < L := hq1 i him
      obtain ⟨j, hjn, hj⟩ := (hr4 (q i) hqL).mp ((hq4 (q i) hqL).mpr ⟨i, him, rfl⟩)
      have hji : j < i := by
        by_contra hc
        push Not at hc
        rcases Nat.eq_or_lt_of_le hc with h' | h'
        · rw [← h'] at hj
          omega
        · have hlt := hr2 i j hjn.le h'
          omega
      have h1 : r j ≤ q j := ih j (by omega) (by omega) (by omega)
      have h2 : q j < q i := hq2 j i him.le hji
      omega
  intro i hin him
  exact main (i + 1) i (Nat.lt_succ_self i) hin him
private theorem strictMono_enumeration_unique {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr1 : ∀ i, i < n → r i < L)
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hrn : r n = L)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hqm : q m = L)
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    n = m ∧ ∀ i, i ≤ n → r i = q i := by
  have le1 := strictMono_enumeration_le hr2 hq1 hq2 hr4 hq4
  have le2 := strictMono_enumeration_le hq2 hr1 hr2 hq4 hr4
  have heq : ∀ i, i < n → i < m → r i = q i := fun i h1 h2 =>
    le_antisymm (le1 i h1 h2) (le2 i h2 h1)
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heqnm | hgt
    · exfalso
      have hqn : q n < L := hq1 n hlt
      obtain ⟨j, hjn, hj⟩ := (hr4 (q n) hqn).mp ((hq4 (q n) hqn).mpr ⟨n, hlt, rfl⟩)
      have ha : r j = q j := heq j hjn (hjn.trans hlt)
      have hb : q j < q n := hq2 j n hlt.le hjn
      omega
    · exact heqnm
    · exfalso
      have hrm : r m < L := hr1 m hgt
      obtain ⟨j, hjm, hj⟩ := (hq4 (r m) hrm).mp ((hr4 (r m) hrm).mpr ⟨m, hgt, rfl⟩)
      have ha : r j = q j := heq j (hjm.trans hgt) hjm
      have hb : r j < r m := hr2 j m hgt.le hjm
      omega
  refine ⟨hnm, ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [h, hrn, hnm, hqm]
  · exact heq i h (by omega)
namespace IsPullbackBlowupSequence
end IsPullbackBlowupSequence
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
namespace FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
theorem _root_.solution {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (h' : IsPullbackBlowupSequence φ s'' s) : s'.Isomorphic s'' := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩ := h'
  obtain ⟨hnm, hall⟩ := strictMono_enumeration_unique hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4
  refine ⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq φ s (hall i hi) ≪≫
    (G i (le_of_le_of_eq hi hnm)).symm, ?_, ?_, ?_⟩
  · have hG0 : (G 0 (le_of_le_of_eq (Nat.zero_le _) hnm)).inv ≫ s''.projectionToBase 0
        = Limits.pullback.fst φ (s.projectionToBase (q 0)) := by
      rw [← gfst 0 (le_of_le_of_eq (Nat.zero_le _) hnm)]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst, hfst 0 (Nat.zero_le _),
      s'.projectionToBase_zero]
  · intro i hi
    have hr : r i ≤ r (i + 1) := (hr2 i (i + 1) hi (Nat.lt_succ_self i)).le
    have hq' : q i ≤ q (i + 1) :=
      (hq2 i (i + 1) (le_of_le_of_eq hi hnm) (Nat.lt_succ_self i)).le
    have h1 := hstepE i hi hr
    have h2 := gstep i (lt_of_lt_of_eq hi hnm) hq'
    have hGinv : (G (i + 1) (le_of_le_of_eq hi hnm)).inv ≫ s''.transitionMapSucc i
        = s.pullbackTransitionMap φ hq' ≫ (G i (le_of_le_of_eq (Nat.le_of_succ_le hi) hnm)).inv := by
      rw [← Iso.cancel_iso_hom_left (G (i + 1) (le_of_le_of_eq hi hnm)), ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp, ← Category.assoc, ← h2]
      simp
    have htrans := pullbackIsoOfEq_hom_comp_pullbackTransitionMap φ s (hall i (Nat.le_of_succ_le hi))
      (hall (i + 1) hi) hr hq'
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hGinv]
    rw [reassoc_of% h1, reassoc_of% htrans]
  · intro i hi
    have h1 := hcen i hi
    have h2 := gcen i (lt_of_lt_of_eq hi hnm)
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [h2, h1, ← Scheme.IdealSheafData.comap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact comap_pullbackIsoOfEq φ s (hall i (Nat.le_of_succ_le hi)) _
end FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence
