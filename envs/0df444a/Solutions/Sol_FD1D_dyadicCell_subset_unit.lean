-- Prove2me | solution 1 for FD1D.dyadicCell_subset_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:04.617845+00:00
-- url     : https://prove2.me/submissions/2661c858-59f9-4555-8d07-39f1fb46fe9f

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
namespace FD1D
theorem _root_.solution {L : ℕ} (i : DyadicNode L) :
    dyadicCell i ⊆ Icc (0 : ℝ) 1 := by
  intro z hz
  have hi0 : 0 ≤ (i.val : ℝ) := by positivity
  have hi1 : (i.val : ℝ) + 1 ≤ (2 ^ L : ℕ) := by
    exact_mod_cast i.isLt
  constructor
  · exact le_trans (div_nonneg (by positivity)
      (by exact_mod_cast (Nat.two_pow_pos L).le)) hz.1
  · calc
      z ≤ dyadicCellLeft i + dyadicCellWidth L := hz.2
      _ = ((i.val : ℝ) + 1) / ((2 ^ L : ℕ) : ℝ) := by
        simp [dyadicCellLeft, dyadicCellWidth]
        ring
      _ ≤ 1 := by
        have hpow : (0 : ℝ) < (2 ^ L : ℕ) := by
          exact_mod_cast Nat.two_pow_pos L
        rw [div_le_one hpow]
        exact_mod_cast hi1
end FD1D
