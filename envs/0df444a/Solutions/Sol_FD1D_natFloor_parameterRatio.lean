-- Prove2me | solution 1 for FD1D.natFloor_parameterRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:59.221283+00:00
-- url     : https://prove2.me/submissions/505a89da-9bd4-457a-84eb-7fbbd7706973

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
    ⌊(m : ℝ) / (parameterA m : ℝ)⌋₊ = m / parameterA m := by
  simpa using
    (Nat.floor_div_natCast (m : ℝ) (parameterA m))
end FD1D
