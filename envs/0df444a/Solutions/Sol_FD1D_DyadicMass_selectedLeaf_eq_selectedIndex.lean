-- Prove2me | solution 1 for FD1D.DyadicMass.selectedLeaf_eq_selectedIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:17.750687+00:00
-- url     : https://prove2.me/submissions/c9749eb8-261e-4231-b39c-e78c1e08b1cb

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
theorem _root_.solution {L : ℕ} (q : DyadicMass L) (u : ℝ) :
    q.selectedLeaf u =
      (q.selectedIndex u).val / ((2 ^ L : ℕ) : ℝ) := by
  induction q generalizing u with
  | leaf =>
      simp [selectedLeaf, selectedIndex]
  | @branch L left right ihLeft ihRight =>
      simp only [selectedLeaf, selectedIndex]
      by_cases hu : u ≤ left.total
      · rw [if_pos hu, if_pos hu, ihLeft]
        simp only [dyadicLeafSumEquiv_inl_val, pow_succ]
        have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by
          exact_mod_cast (pow_ne_zero L (by decide : (2 : ℕ) ≠ 0))
        norm_num
        field_simp [hpow]
      · rw [if_neg hu, if_neg hu, ihRight]
        simp only [dyadicLeafSumEquiv_inr_val, pow_succ]
        have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by
          exact_mod_cast (pow_ne_zero L (by decide : (2 : ℕ) ≠ 0))
        norm_num
        field_simp [hpow]
end FD1D.DyadicMass
