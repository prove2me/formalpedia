-- Prove2me | solution 1 for FD1D.leafCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:07.347422+00:00
-- url     : https://prove2.me/submissions/44439ad3-4ff4-48b1-ad57-cb1b9a42b321

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
    0 < leafCount m := by
  simp [leafCount]
end FD1D
