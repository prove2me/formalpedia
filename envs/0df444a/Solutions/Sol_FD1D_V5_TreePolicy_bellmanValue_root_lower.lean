-- Prove2me | solution 1 for FD1D.V5.TreePolicy.bellmanValue_root_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:49.050707+00:00
-- url     : https://prove2.me/submissions/f7a384b4-5c33-4212-a839-2b1c2d48289e

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_bellmanValue_root_eq
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.rate_root
attribute [local simp] FD1D.V5.TreePolicy.rate_leftChild
attribute [local simp] FD1D.V5.TreePolicy.rate_rightChild
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_root
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_leftChild
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_rightChild

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    -(1 / (2 * (m : ℝ) ^ 2)) ≤
      bellmanValue I a 0 dyadicRoot := by
  rw [bellmanValue_root_eq I ha hm]
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsmall :
      2 * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) * ((m : ℝ) + a / 2) := by
    nlinarith [mul_pos hmR ha]
  have hrecip :
      1 / (2 * (m : ℝ) * ((m : ℝ) + a / 2)) ≤
        1 / (2 * (m : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le (by positivity) hsmall
  simpa only [neg_div] using neg_le_neg hrecip
end FD1D.V5.TreePolicy
