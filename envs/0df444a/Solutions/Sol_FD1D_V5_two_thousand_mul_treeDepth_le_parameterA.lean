-- Prove2me | solution 1 for FD1D.V5.two_thousand_mul_treeDepth_le_parameterA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:23.023523+00:00
-- url     : https://prove2.me/submissions/b11d25be-98f1-4ef8-8708-721b92e42be8

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_treeDepth_le_clog
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ}
    (hm : 1 ≤ m) :
    2000 * treeDepth m ≤ parameterA m := by
  simpa [parameterA] using
    Nat.mul_le_mul_left 2000 (treeDepth_le_clog hm)
end FD1D.V5
