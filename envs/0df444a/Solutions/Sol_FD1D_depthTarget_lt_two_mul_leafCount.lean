-- Prove2me | solution 1 for FD1D.depthTarget_lt_two_mul_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:13.613535+00:00
-- url     : https://prove2.me/submissions/a16cbba6-b5e0-4c04-8226-e6ce1e589f48

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.natFloor_parameterRatio
attribute [local simp] FD1D.leafCount_eq_pow

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    depthTarget m < 2 * leafCount m := by
  change depthTarget m < 2 * 2 ^ Nat.log 2 (depthTarget m)
  simpa [pow_succ'] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (depthTarget m))
end FD1D
