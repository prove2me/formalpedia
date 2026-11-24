-- Prove2me | solution 1 for FairChores.exists_assignform_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:27.527204+00:00
-- url     : https://prove2.me/submissions/033c8d84-ab6b-4855-807b-b0cd33e526db

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (hn : 0 < n) (c p : T → ℝ) (o : Outcome T n) (ho : o.Valid p) :
    ∃ (assign : T → Option (Fin n)) (m : Fin n → ℝ),
      (∀ j, 0 ≤ m j) ∧ (billOf p assign ≤ ∑ j, m j) ∧
      maxCostData c assign m ≤ maxCost c o := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hdo, hdk, hcov, hm0, hbudget⟩ := ho
  set assign : T → Option (Fin n) :=
    fun t => if t ∈ o.outsourced then none
      else (if h : ∃ j, t ∈ o.kept j then some h.choose else some ⟨0, hn⟩) with hassign
  have hnone : ∀ t, assign t = none ↔ t ∈ o.outsourced := by
    intro t
    constructor
    · intro h
      by_contra hts
      simp only [hassign, if_neg hts] at h
      split at h <;> simp_all
    · intro h; simp only [hassign, if_pos h]
  have hkept : ∀ j t, t ∈ o.kept j → assign t = some j := by
    intro j t ht
    have hts : t ∉ o.outsourced := Finset.disjoint_right.mp (hdo j) ht
    have hex : ∃ k, t ∈ o.kept k := ⟨j, ht⟩
    simp only [hassign, if_neg hts, dif_pos hex]
    have hc : t ∈ o.kept hex.choose := hex.choose_spec
    by_cases hkj : hex.choose = j
    · rw [hkj]
    · exact absurd (Finset.disjoint_left.mp (hdk _ _ hkj) hc ht) (by simp)
  have hsub : ∀ j, Finset.univ.filter (fun t => assign t = some j) ⊆ o.kept j := by
    intro j t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hts : t ∉ o.outsourced := by
      intro hcon
      rw [(hnone t).mpr hcon] at ht; exact absurd ht (by simp)
    have hmem : t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept := by
      rw [hcov]; exact Finset.mem_univ t
    rcases Finset.mem_union.mp hmem with h | h
    · exact absurd h hts
    · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp h
      have := hkept k t hk
      rw [this] at ht
      have : k = j := Option.some.inj ht
      rwa [this] at hk
  refine ⟨assign, o.pay, hm0, ?_, ?_⟩
  · have hset : Finset.univ.filter (fun t => assign t = none) = o.outsourced := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnone t]
    rw [billOf, hset]; exact hbudget
  · refine ciSup_mono (Finite.bddAbove_range _) (fun j => ?_)
    show keptCost c assign j + o.pay j ≤ cost c o j
    simp only [cost, keptCost]
    have heq : Finset.univ.filter (fun t => assign t = some j) = o.kept j := by
      apply Finset.Subset.antisymm (hsub j)
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hkept j t ht
    rw [heq]
end FairChores
