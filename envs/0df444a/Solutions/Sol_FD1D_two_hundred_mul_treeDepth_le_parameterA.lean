-- Prove2me | solution 1 for FD1D.two_hundred_mul_treeDepth_le_parameterA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:16.426772+00:00
-- url     : https://prove2.me/submissions/d2f6da82-b40b-4c52-81ed-e57827bd41c1

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_treeDepth_le_clog
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.natFloor_parameterRatio

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ}
    (hm : 1 ≤ m) :
    200 * treeDepth m ≤ parameterA m := by
  simpa [parameterA] using
    Nat.mul_le_mul_left 200 (treeDepth_le_clog hm)
end FD1D
