-- Prove2me | solution 1 for FairSelling.compose_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:33.745673+00:00
-- url     : https://prove2.me/submissions/139e7d6d-ea72-442b-a3aa-fdd48d12bc02

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_sum_restrictVal
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_fin3_sum
import Theorems.Thm_FairSelling_sum_le_vbarSum
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome

attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ka Sa : Finset G) (ma : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hmaS : ma ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome G 2)
    (ho2 : o2.Valid (restrictVal (Finset.univ \ (Ka ∪ Sa)) p))
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hc : (3/4 : ℝ) * MMS 3 (v c) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v c)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  set R : Finset G := Finset.univ \ (Ka ∪ Sa) with hR
  obtain ⟨ho2_sold, ho2_disj, ho2_money, ho2_budget⟩ := ho2
  -- Disjointness of `Ka` and `Sa` with the remaining goods `R`.
  have hKaR : Disjoint Ka R := by
    rw [hR]
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxR
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_left _ hx)
  have hSaR : Disjoint Sa R := by
    rw [hR]
    refine Finset.disjoint_left.mpr ?_
    intro x hx hxR
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_right _ hx)
  -- The three groups handed out in full.
  set Avec : Fin 3 → Finset G :=
    fun i => if i = a then Ka else if i = b then o2.kept 0 ∩ R else o2.kept 1 ∩ R with hAvec
  set F : Finset G := Sa ∪ (o2.sold ∩ R) with hF
  set q : Fin 3 → ℝ :=
    fun i => if i = a then ma else if i = b then o2.money 0 else o2.money 1 with hq
  -- Evaluations of `Avec` and `q`.
  have hAveca : Avec a = Ka := by simp [hAvec]
  have hAvecb : Avec b = o2.kept 0 ∩ R := by simp [hAvec, (Ne.symm hab)]
  have hAvecc : Avec c = o2.kept 1 ∩ R := by simp [hAvec, (Ne.symm hac), (Ne.symm hbc)]
  have hqa : q a = ma := by simp [hq]
  have hqb : q b = o2.money 0 := by simp [hq, (Ne.symm hab)]
  have hqc : q c = o2.money 1 := by simp [hq, (Ne.symm hac), (Ne.symm hbc)]
  refine ⟨unifiedOutcome v p Avec F q, ?_, ?_⟩
  · -- Validity.
    apply unifiedOutcome_valid v p hp Avec F q
    · -- pairwise disjoint groups
      intro i j hij
      rcases fin3_cover hab hac hbc i with hi | hi | hi <;>
        rcases fin3_cover hab hac hbc j with hj | hj | hj <;>
        subst hi <;> subst hj <;> first
          | exact absurd rfl hij
          | (rw [hAveca, hAvecb]; exact (hKaR.mono_right Finset.inter_subset_right))
          | (rw [hAveca, hAvecc]; exact (hKaR.mono_right Finset.inter_subset_right))
          | (rw [hAvecb, hAveca];
             exact ((hKaR.mono_right Finset.inter_subset_right).symm))
          | (rw [hAvecc, hAveca];
             exact ((hKaR.mono_right Finset.inter_subset_right).symm))
          | (rw [hAvecb, hAvecc];
             exact ((ho2_disj 0 1 (by decide)).mono
               Finset.inter_subset_left Finset.inter_subset_left))
          | (rw [hAvecc, hAvecb];
             exact ((ho2_disj 1 0 (by decide)).mono
               Finset.inter_subset_left Finset.inter_subset_left))
    · -- `F` disjoint from each group
      intro i
      rw [hF, Finset.disjoint_union_left]
      rcases fin3_cover hab hac hbc i with hi | hi | hi <;> subst hi
      · rw [hAveca]
        exact ⟨hKSa.symm, (hKaR.mono_right Finset.inter_subset_right).symm⟩
      · rw [hAvecb]
        refine ⟨hSaR.mono_right Finset.inter_subset_right, ?_⟩
        exact ((ho2_sold 0).mono Finset.inter_subset_left Finset.inter_subset_left)
      · rw [hAvecc]
        refine ⟨hSaR.mono_right Finset.inter_subset_right, ?_⟩
        exact ((ho2_sold 1).mono Finset.inter_subset_left Finset.inter_subset_left)
    · -- nonnegative money
      intro i
      rcases fin3_cover hab hac hbc i with hi | hi | hi <;> subst hi
      · rw [hqa]; exact hma0
      · rw [hqb]; exact ho2_money 0
      · rw [hqc]; exact ho2_money 1
    · -- budget
      rw [fin3_sum hab hac hbc q, hqa, hqb, hqc]
      have hFdisj : Disjoint Sa (o2.sold ∩ R) := hSaR.mono_right Finset.inter_subset_right
      have hFsum : ∑ g ∈ F, p g = (∑ g ∈ Sa, p g) + ∑ g ∈ o2.sold ∩ R, p g := by
        rw [hF, Finset.sum_union hFdisj]
      have hbudget2 : o2.money 0 + o2.money 1 ≤ ∑ g ∈ o2.sold ∩ R, p g := by
        have := ho2_budget
        rw [Fin.sum_univ_two] at this
        rwa [sum_restrictVal R p o2.sold] at this
      rw [hFsum]; linarith [hmaS]
  · -- Utilities.
    intro i
    rw [util_unifiedOutcome v p Avec F q i]
    rcases fin3_cover hab hac hbc i with hi | hi | hi
    · rw [hi, hAveca, hqa]; exact haU
    · rw [hi, hAvecb, hqb]
      have hutil : util (restrictVal R (v b)) o2 0
          = (∑ g ∈ o2.kept 0 ∩ R, v b g) + o2.money 0 := by
        rw [util, sum_restrictVal R (v b) (o2.kept 0)]
      have hge : (∑ g ∈ o2.kept 0 ∩ R, v b g) ≤ vbarSum (v b) p (o2.kept 0 ∩ R) :=
        sum_le_vbarSum (v b) p (o2.kept 0 ∩ R)
      have hbb := hb
      rw [hutil] at hbb
      linarith
    · rw [hi, hAvecc, hqc]
      have hutil : util (restrictVal R (v c)) o2 1
          = (∑ g ∈ o2.kept 1 ∩ R, v c g) + o2.money 1 := by
        rw [util, sum_restrictVal R (v c) (o2.kept 1)]
      have hge : (∑ g ∈ o2.kept 1 ∩ R, v c g) ≤ vbarSum (v c) p (o2.kept 1 ∩ R) :=
        sum_le_vbarSum (v c) p (o2.kept 1 ∩ R)
      have hcc := hc
      rw [hutil] at hcc
      linarith
end FairSelling
