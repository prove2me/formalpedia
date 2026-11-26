-- Prove2me | solution 1 for FD1D.V5.leafCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:29.107092+00:00
-- url     : https://prove2.me/submissions/5ed6d6cf-2641-4b73-988f-ec7d84e20423

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution (m : ℕ) :
    0 < leafCount m := by
  simp [leafCount]
end FD1D.V5
