-- Prove2me | solution 1 for FairSelling.GeneralTPS.total_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:09.496658+00:00
-- url     : https://prove2.me/submissions/105021dc-8d41-458d-aa4c-0d780e8738a6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hp : ∀ g, 0 ≤ p g)
    {s : Stage G n} (hs : s.Good v p eps) :
    s.total v p ≤ totalBound v p := by
  classical
  have h1 : ∀ i, vbarSum (v i) p (s.bundle i) ≤ vbarSum (v i) p Finset.univ := by
    intro i
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro g _ _
    exact le_trans (hp g) (le_max_left _ _)
  have h2 : (∑ i, s.cash i) ≤ ∑ g, p g := by
    have hb := hs.2.2.2.2.1
    have hsum := hs.2.2.2.2.2.1
    have : ∑ g ∈ s.soldSet, p g ≤ ∑ g, p g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun g _ _ => hp g)
    linarith
  unfold Stage.total totalBound
  rw [Finset.sum_add_distrib]
  exact add_le_add (Finset.sum_le_sum (fun i _ => h1 i)) h2
end FairSelling.GeneralTPS
