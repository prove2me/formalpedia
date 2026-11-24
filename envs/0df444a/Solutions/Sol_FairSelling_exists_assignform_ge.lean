-- Prove2me | solution 1 for FairSelling.exists_assignform_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:59.262852+00:00
-- url     : https://prove2.me/submissions/506300b7-4883-41d3-9746-3e8314674df8

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g)
    (o : Outcome G n) (ho : o.Valid p) :
    ∃ (assign : G → Option (Fin n)) (m : Fin n → ℝ),
      (∀ j, 0 ≤ m j) ∧ (∑ j, m j ≤ procOf p assign) ∧
      minUtil v o ≤ minUtilData v assign m := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hsold, hdisj, hmoney, hbudget⟩ := ho
  set assign : G → Option (Fin n) :=
    fun g => if g ∈ o.sold then none
      else (if h : ∃ j, g ∈ o.kept j then some h.choose else some ⟨0, hn⟩) with hassign
  have hnone : ∀ g, assign g = none ↔ g ∈ o.sold := by
    intro g
    constructor
    · intro h
      by_contra hgs
      simp only [hassign, if_neg hgs] at h
      split at h <;> simp_all
    · intro h; simp only [hassign, if_pos h]
  have hkept : ∀ j g, g ∈ o.kept j → assign g = some j := by
    intro j g hg
    have hgs : g ∉ o.sold := Finset.disjoint_right.mp (hsold j) hg
    have hex : ∃ k, g ∈ o.kept k := ⟨j, hg⟩
    simp only [hassign, if_neg hgs, dif_pos hex]
    have hc : g ∈ o.kept hex.choose := hex.choose_spec
    by_cases hkj : hex.choose = j
    · rw [hkj]
    · exact absurd (Finset.disjoint_left.mp (hdisj _ _ hkj) hc hg) (by simp)
  refine ⟨assign, o.money, hmoney, ?_, ?_⟩
  · have hset : Finset.univ.filter (fun g => assign g = none) = o.sold := by
      ext g; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnone g]
    rw [procOf, hset]; exact hbudget
  · apply ciInf_mono (Finite.bddBelow_range _)
    intro j
    have hsub : o.kept j ⊆ Finset.univ.filter (fun g => assign g = some j) := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hkept j g hg
    have hle : (∑ g ∈ o.kept j, v g) ≤ keptVal v assign j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hv i)
    show util v o j ≤ keptVal v assign j + o.money j
    simp only [util]; linarith [hle]
end FairSelling
