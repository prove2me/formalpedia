-- Prove2me | solution 1 for FD1D.DyadicMass.selectedLeaf_le_quantile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:28.888607+00:00
-- url     : https://prove2.me/submissions/95005f4b-081b-4358-8abd-42c55b131537

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.selectedLeaf u ≤ q.quantile u := by
  induction q generalizing u with
  | leaf mass =>
      simp only [selectedLeaf, quantile]
      exact (quantile_mem_unit (leaf mass) hq hu0 hu1).1
  | @branch L left right ihLeft ihRight =>
      simp only [selectedLeaf, quantile]
      by_cases hu : u ≤ left.total
      · rw [if_pos hu, if_pos hu]
        exact div_le_div_of_nonneg_right
          (ihLeft hq.1 hu0 hu) (by norm_num)
      · rw [if_neg hu, if_neg hu]
        have huLocal0 : 0 ≤ u - left.total := by linarith
        have huLocal1 : u - left.total ≤ right.total := by
          rw [total] at hu1
          linarith
        have hlocal := ihRight hq.2 huLocal0 huLocal1
        apply div_le_div_of_nonneg_right _ (by norm_num)
        linarith
end FD1D.DyadicMass
