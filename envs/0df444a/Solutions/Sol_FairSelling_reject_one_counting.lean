-- Prove2me | solution 1 for FairSelling.reject_one_counting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:00:53.538841+00:00
-- url     : https://prove2.me/submissions/0da4c0e9-7210-4cc0-9a1b-7cf1659dd1a7

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_four_thr_le_vbarSum_univ
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (K S : Finset G) (m : ℝ)
    (hS : vbarSum w p S ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p))
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p + m ≤ vbarSum w p (Finset.univ \ (K ∪ S)) := by
  classical
  have hsub : K ∪ S ⊆ Finset.univ := Finset.subset_univ _
  have hsdiff := vbarSum_sdiff w p hsub
  have htot := four_thr_le_vbarSum_univ w p hw hp
  have hKS : vbarSum w p (K ∪ S) ≤ vbarSum w p K + vbarSum w p S := by
    have hunion : K ∪ S = K ∪ (S \ K) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    have hdisj : Disjoint K (S \ K) := Finset.disjoint_sdiff
    have hle : vbarSum w p (S \ K) ≤ vbarSum w p S := by
      simp only [vbarSum]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun g _ _ => le_max_of_le_left (hp g))
    rw [hunion, vbarSum_union w p hdisj]
    linarith
  rw [hsdiff]
  linarith
end FairSelling
