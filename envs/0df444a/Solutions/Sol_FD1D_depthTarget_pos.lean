-- Prove2me | solution 1 for FD1D.depthTarget_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:40.821935+00:00
-- url     : https://prove2.me/submissions/3e14752c-1141-47fb-84a7-d895c1e36d92

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.natFloor_parameterRatio

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    0 < depthTarget m := by
  simp [depthTarget]
end FD1D
