-- Prove2me | solution 1 for FD1D.harmonicPotential_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:38.510567+00:00
-- url     : https://prove2.me/submissions/fa4db363-99c5-4a56-a985-4d23cb3dc28d

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (a : ℝ) :
    harmonicPotential a 0 = 0 := by
  simp [harmonicPotential]
end FD1D
