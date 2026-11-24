-- Prove2me | solution 1 for FairSelling.EF1alloc_of_SEF1_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:28.832404+00:00
-- url     : https://prove2.me/submissions/f83c153b-909a-4459-a5b5-68ff923d9878

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Theorems.Thm_FairSelling_vbarSum_eq_sum_of_price_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (p : G → ℝ)
    (hp : ∀ g, p g = 0) (o : Outcome G n) (hfull : o.Full p ∅) (hsef1 : SEF1 v p o) :
    IsPartitionOf o.kept Finset.univ ∧ EF1alloc v o.kept := by
  obtain ⟨hvalid, hsub, hall, hmsum⟩ := hfull
  have hsold : o.sold = ∅ := Finset.subset_empty.mp hsub
  have hmoney : ∀ j, o.money j = 0 := by
    intro j
    refine le_antisymm ?_ (hvalid.2.2.1 j)
    have h1 : ∑ k, o.money k = 0 := by rw [hmsum, hsold]; simp
    have h2 : o.money j ≤ ∑ k, o.money k :=
      Finset.single_le_sum (f := o.money) (fun k _ => hvalid.2.2.1 k) (Finset.mem_univ j)
    linarith
  refine ⟨⟨hvalid.2.1, ?_⟩, ?_⟩
  · have := hall
    rw [Outcome.AllocatesAll, hsold] at this
    simpa using this
  · intro i j hne
    have hbi : vbarSum (v i) p (o.kept i) = ∑ g' ∈ o.kept i, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    have hbj : vbarSum (v i) p (o.kept j) = ∑ g' ∈ o.kept j, v i g' :=
      vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g)
    rcases (hsef1 i j).2 (hmoney j) with hEF | ⟨g, hg, hx⟩
    · obtain ⟨g, hg⟩ := hne
      refine ⟨g, hg, ?_⟩
      rw [hbi, hbj, hmoney i] at hEF
      have hsub : ∑ g' ∈ o.kept j \ {g}, v i g' ≤ ∑ g' ∈ o.kept j, v i g' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun g' _ _ => hv i g')
      linarith
    · refine ⟨g, hg, ?_⟩
      rw [hbi, vbarSum_eq_sum_of_price_zero (fun g => hv i g) (fun g _ => hp g), hp g,
        hmoney i] at hx
      linarith
end FairSelling
