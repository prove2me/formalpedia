-- Prove2me | solution 1 for FairSelling.util_unifiedOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:45.765919+00:00
-- url     : https://prove2.me/submissions/94d9f590-06fb-48b1-a3e2-0139ef55ad9f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    util (v i) (unifiedOutcome v p A F q) i = vbarSum (v i) p (A i) + q i := by
  classical
  simp only [util, unifiedOutcome, vbarSum, vbar]
  rw [← Finset.sum_filter_add_sum_filter_not (A i) (fun g => v i g < p g)
        (fun g => max (p g) (v i g))]
  have h1 : ∑ g ∈ (A i).filter (fun g => v i g < p g), max (p g) (v i g)
      = ∑ g ∈ (A i).filter (fun g => v i g < p g), p g := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [Finset.mem_filter] at hg
    exact max_eq_left (le_of_lt hg.2)
  have h2 : ∑ g ∈ (A i).filter (fun g => ¬ v i g < p g), max (p g) (v i g)
      = ∑ g ∈ (A i).filter (fun g => ¬ v i g < p g), v i g := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    simp only [Finset.mem_filter, not_lt] at hg
    exact max_eq_right hg.2
  rw [h1, h2]; ring
end FairSelling
