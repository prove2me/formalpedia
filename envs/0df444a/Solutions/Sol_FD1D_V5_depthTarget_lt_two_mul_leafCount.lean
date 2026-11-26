-- Prove2me | solution 1 for FD1D.V5.depthTarget_lt_two_mul_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:43.213117+00:00
-- url     : https://prove2.me/submissions/52f936d5-b3a7-41cb-a172-d7ea744088d9

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution (m : ℕ) :
    depthTarget m < 2 * leafCount m := by
  change depthTarget m < 2 * 2 ^ Nat.log 2 (depthTarget m)
  simpa [pow_succ'] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (depthTarget m))
end FD1D.V5
