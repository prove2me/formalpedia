-- Prove2me | solution 1 for FairSelling.Canonical.cash_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:47.126479+00:00
-- url     : https://prove2.me/submissions/61b6cb0d-66e0-4b90-9179-391b9f31c7e1

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Theorems.Thm_FairSelling_Canonical_mem_sold
import Theorems.Thm_FairSelling_Canonical_sold_subset_sell

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]
namespace FairSelling.Canonical
theorem _root_.solution (C : Canonical w p μ t k R D) (J : Finset (Fin k)) :
    ∑ j ∈ J, C.cash j ≤ D + ∑ g ∈ C.sold J, p g := by
  classical
  have hd : ∑ j ∈ J, C.dcash j ≤ D := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun j _ _ => C.dcash_nonneg j)) C.dcash_sum
  have hs : ∑ j ∈ J, C.scash j ≤ ∑ g ∈ C.sold J, p g := by
    set t' : Finset (Option G) := insert none ((C.sold J).image some) with ht'
    have hmaps : ∀ j ∈ J, C.src j ∈ t' := by
      intro j hj
      cases hsrc : C.src j with
      | none => ?_
      | some f => ?_
      · simp [ht']
      · refine Finset.mem_insert_of_mem ?_
        exact Finset.mem_image_of_mem _ (mem_sold.mpr ⟨j, hj, hsrc⟩)
    have hfib := Finset.sum_fiberwise_of_maps_to hmaps C.scash
    have hnone : ∑ j ∈ J.filter (fun j => C.src j = none), C.scash j = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      exact C.scash_zero j (Finset.mem_filter.mp hj).2
    have hsome : ∀ f ∈ C.sold J,
        ∑ j ∈ J.filter (fun j => C.src j = some f), C.scash j ≤ p f := by
      intro f hf
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => C.scash_nonneg j))
        (C.scash_sum f (C.sold_subset_sell J hf))
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.2
    have hsplit : ∑ y ∈ t', ∑ j ∈ J.filter (fun j => C.src j = y), C.scash j
        = (∑ j ∈ J.filter (fun j => C.src j = none), C.scash j)
          + ∑ y ∈ (C.sold J).image some, ∑ j ∈ J.filter (fun j => C.src j = y), C.scash j := by
      rw [ht', Finset.sum_insert (by simp)]
    rw [hsplit, hnone, zero_add] at hfib
    rw [← hfib, Finset.sum_image (fun x _ y _ h => Option.some_injective _ h)]
    exact Finset.sum_le_sum hsome
  simp only [cash, Finset.sum_add_distrib]
  linarith
end FairSelling.Canonical
