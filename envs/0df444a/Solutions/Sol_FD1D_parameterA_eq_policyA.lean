-- Prove2me | solution 1 for FD1D.parameterA_eq_policyA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:14.773462+00:00
-- url     : https://prove2.me/submissions/d3319a6c-6515-4916-ac21-0d4d40f7403e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.policyA_eq_parameterA

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    parameterA m = policyA m :=
  (policyA_eq_parameterA m).symm
end FD1D
