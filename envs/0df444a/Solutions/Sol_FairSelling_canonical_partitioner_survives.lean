-- Prove2me | solution 1 for FairSelling.canonical_partitioner_survives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:11.140371+00:00
-- url     : https://prove2.me/submissions/34975372-711f-4dab-888d-15b48ddbe1dc

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_MMS2_cash_of_two_bundles_sell
import Theorems.Thm_FairSelling_fin3_others
import Theorems.Thm_FairSelling_fin3_sum


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ} {lo : Fin 3}
    (hcan : IsCanonical w p τ kept sold money lo)
    (k : Fin 3) (Sa : Finset G) (hSa : Sa ⊆ sold) (hfund : money k ≤ ∑ g ∈ Sa, p g) :
    τ ≤ MMS 2 (cashVal (Finset.univ \ (kept k ∪ Sa)) w)
      (cashPrice (Finset.univ \ (kept k ∪ Sa)) p ((∑ g ∈ Sa, p g) - money k)) := by
  classical
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := hcan
  obtain ⟨j, j', hjk, hj'k, hjj'⟩ := fin3_others k
  set R : Finset G := Finset.univ \ (kept k ∪ Sa) with hR
  have hsub : ∀ B : Finset G, Disjoint B (kept k) → Disjoint B Sa → B ⊆ R := by
    intro B h1 h2 x hx
    rw [hR, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_union]
    rintro (h | h)
    · exact (Finset.disjoint_left.mp h1 hx) h
    · exact (Finset.disjoint_left.mp h2 hx) h
  have hjR : kept j ⊆ R :=
    hsub _ (hdisj _ _ hjk) (Finset.disjoint_of_subset_right hSa (hsold j).symm)
  have hj'R : kept j' ⊆ R :=
    hsub _ (hdisj _ _ hj'k) (Finset.disjoint_of_subset_right hSa (hsold j').symm)
  have hTR : sold \ Sa ⊆ R :=
    hsub _ (Finset.disjoint_of_subset_left Finset.sdiff_subset (hsold k))
      (Finset.sdiff_disjoint)
  have hsplit : (∑ g ∈ Sa, p g) + ∑ g ∈ sold \ Sa, p g = ∑ g ∈ sold, p g := by
    rw [add_comm]; exact Finset.sum_sdiff hSa
  have hsum3 : ∑ i, money i = money k + money j + money j' := by
    rcases fin3_others k with -
    have : ∀ f : Fin 3 → ℝ, ∑ i, f i = f k + f j + f j' :=
      fun f => fin3_sum (Ne.symm hjk) (Ne.symm hj'k) hjj' f
    exact this money
  refine MMS2_cash_of_two_bundles_sell w p hw hp R (kept j) (kept j') (sold \ Sa)
    ((∑ g ∈ Sa, p g) - money k) (money j) (money j') τ
    (hdisj _ _ hjj')
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (hsold j).symm)
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (hsold j').symm)
    hjR hj'R hTR (by linarith) (hm0 j) (hm0 j') ?_ (hacc j) (hacc j')
  have := hm0 k
  linarith [hmsum, hsum3, hsplit]
end FairSelling
