-- Prove2me | solution 1 for FD1D.harmonicPotential_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:56.516217+00:00
-- url     : https://prove2.me/submissions/62878427-f974-4966-be77-006dc4e497aa

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.harmonicPotential_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (a : ℝ) (k : ℕ) :
    harmonicPotential a (k + 1) =
      harmonicPotential a k + 1 / (k + 1 + a) := by
  rw [harmonicPotential, harmonicPotential, Finset.sum_Icc_succ_top]
  · simp [add_comm, add_left_comm, add_assoc]
  · omega
end FD1D
