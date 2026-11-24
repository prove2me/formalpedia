-- Prove2me | solution 1 for FairSelling.losses_extend_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:33.234638+00:00
-- url     : https://prove2.me/submissions/7252ae98-577d-48f7-a7c4-a3b2418a0a8e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


section
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G] in
private lemma sum_ite_mem_split {M : Type*} [AddCommMonoid M] (K : Finset (Fin n))
    (x y : Fin n → M) :
    ∑ b, (if b ∈ K then x b else y b) = (∑ b ∈ K, x b) + ∑ b ∈ Finset.univ \ K, y b := by
  classical
  rw [← Finset.sum_sdiff (Finset.subset_univ K), add_comm]
  congr 1
  · exact Finset.sum_congr rfl (fun b hb => by simp [hb])
  · exact Finset.sum_congr rfl (fun b hb => by simp [(Finset.mem_sdiff.mp hb).2])
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D) {Kset : Finset (Fin n)} (hKT : Kset ⊆ T)
    (Ea Fa : Fin n → Finset G) (ca : Fin n → ℝ)
    (hEsub : ∀ b ∈ Kset, Ea b ⊆ R) (hFsub : ∀ b ∈ Kset, Fa b ⊆ R)
    (hEF : ∀ b ∈ Kset, Disjoint (Ea b) (Fa b))
    (hpair : ∀ b ∈ Kset, ∀ b' ∈ Kset, b ≠ b' → Disjoint (Ea b ∪ Fa b) (Ea b' ∪ Fa b'))
    (hc0 : ∀ b ∈ Kset, 0 ≤ ca b)
    (htype : ∀ i ∈ T \ Kset, ∀ Ei : EquiMMS (v i) p (MMS n (v i) p) n, ∀ b ∈ Kset,
      LossOK (v i) p Ei.sell (MMS n (v i) p) (thr v p i) (Ea b) (Fa b) (ca b)) :
    Losses v p (T \ Kset) (R \ Kset.biUnion (fun b => Ea b ∪ Fa b))
      (D + (∑ b ∈ Kset, ∑ g ∈ Fa b, p g) - ∑ b ∈ Kset, ca b) := by
  classical
  obtain ⟨alloc, sold, paid, hempty, hdisj1, hdisj2, hdisjR, hcover, hpaid0, hmoney, htypes⟩ := hL
  set U : Finset G := Kset.biUnion (fun b => Ea b ∪ Fa b) with hU
  have hUR : U ⊆ R := by
    intro g hg
    obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.mp hg
    rcases Finset.mem_union.mp hgb with h | h
    · exact hEsub b hb h
    · exact hFsub b hb h
  have hsubU : ∀ b ∈ Kset, Ea b ∪ Fa b ⊆ U := fun b hb g hg => Finset.mem_biUnion.mpr ⟨b, hb, hg⟩
  refine ⟨fun b => if b ∈ Kset then Ea b else alloc b, fun b => if b ∈ Kset then Fa b else sold b,
    fun b => if b ∈ Kset then ca b else paid b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hbK : b ∉ Kset := (Finset.mem_sdiff.mp hb).2
    simp only [if_neg hbK]
    exact hempty b (Finset.mem_sdiff.mp hb).1
  · intro b
    by_cases hb : b ∈ Kset
    · simp only [if_pos hb]; exact hEF b hb
    · simp only [if_neg hb]; exact hdisj1 b
  · intro b b' hbb
    by_cases hb : b ∈ Kset <;> by_cases hb' : b' ∈ Kset
    · simp only [if_pos hb, if_pos hb']; exact hpair b hb b' hb' hbb
    · simp only [if_pos hb, if_neg hb']
      exact Finset.disjoint_of_subset_left ((hsubU b hb).trans hUR) (hdisjR b')
    · simp only [if_neg hb, if_pos hb']
      exact (Finset.disjoint_of_subset_left ((hsubU b' hb').trans hUR) (hdisjR b)).symm
    · simp only [if_neg hb, if_neg hb']; exact hdisj2 b b' hbb
  · intro b
    by_cases hb : b ∈ Kset
    · simp only [if_pos hb]
      exact Finset.disjoint_of_subset_right (hsubU b hb) Finset.sdiff_disjoint
    · simp only [if_neg hb]
      exact Finset.disjoint_of_subset_left Finset.sdiff_subset (hdisjR b)
  · ext g
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_iff, Finset.mem_sdiff]
    have hg : g ∈ R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b) := by
      rw [← hcover]; exact Finset.mem_univ g
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hg
    by_cases hgU : g ∈ U
    · obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.mp hgU
      refine Or.inr ⟨b, ?_⟩
      simp only [if_pos hb]
      exact ⟨trivial, Finset.mem_union.mp hgb⟩
    · rcases hg with hgR | ⟨b, hb⟩
      · exact Or.inl ⟨hgR, hgU⟩
      · by_cases hbK : b ∈ Kset
        · exfalso
          have := hempty b (hKT hbK)
          rw [this.1, this.2.1] at hb
          simp at hb
        · exact Or.inr ⟨b, by simp only [if_neg hbK]; exact ⟨trivial, hb⟩⟩
  · intro b
    by_cases hb : b ∈ Kset
    · simp only [if_pos hb]; exact hc0 b hb
    · simp only [if_neg hb]; exact hpaid0 b
  · have hsold : ∑ b, ∑ g ∈ (if b ∈ Kset then Fa b else sold b), p g
        = (∑ b ∈ Kset, ∑ g ∈ Fa b, p g) + ∑ b, ∑ g ∈ sold b, p g := by
      have h1 : ∑ b, ∑ g ∈ (if b ∈ Kset then Fa b else sold b), p g
          = ∑ b, (if b ∈ Kset then ∑ g ∈ Fa b, p g else ∑ g ∈ sold b, p g) :=
        Finset.sum_congr rfl (fun b _ => by by_cases hb : b ∈ Kset <;> simp [hb])
      rw [h1, sum_ite_mem_split]
      congr 1
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have : ∑ b ∈ Kset, ∑ g ∈ sold b, p g = 0 :=
        Finset.sum_eq_zero (fun b hb => by rw [(hempty b (hKT hb)).2.1]; simp)
      rw [this]; ring
    have hpd : ∑ b, (if b ∈ Kset then ca b else paid b) = (∑ b ∈ Kset, ca b) + ∑ b, paid b := by
      rw [sum_ite_mem_split]
      congr 1
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have : ∑ b ∈ Kset, paid b = 0 :=
        Finset.sum_eq_zero (fun b hb => (hempty b (hKT hb)).2.2)
      rw [this]; ring
    rw [hsold, hpd]
    linarith
  · intro i hi
    obtain ⟨Ei, hEi⟩ := htypes i (Finset.mem_sdiff.mp hi).1
    refine ⟨Ei, ?_⟩
    intro b hb
    by_cases hbK : b ∈ Kset
    · simp only [if_pos hbK]
      exact htype i hi Ei b hbK
    · simp only [if_neg hbK]
      refine hEi b (fun hbT => hb (Finset.mem_sdiff.mpr ⟨hbT, hbK⟩))
end FairSelling
