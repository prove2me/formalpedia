-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.parentMass_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:22.50263+00:00
-- url     : https://prove2.me/submissions/86a16f3f-3938-4b98-a7d0-7c22ec814264

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (h : ℝ) (x y : ℕ) :
    parentMass h y x = parentMass h x y := by
  simp [parentMass, inventory, add_comm]
end FD1D.V5.LocalPolicy
