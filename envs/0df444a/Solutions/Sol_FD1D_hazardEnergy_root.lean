-- Prove2me | solution 1 for FD1D.hazardEnergy_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:23.03699+00:00
-- url     : https://prove2.me/submissions/285340f0-e2b0-4b47-b97f-d4d3b32519ed

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (h : ∀ d, DyadicNode d → ℝ) :
    hazardEnergy h 0 = (h 0 dyadicRoot) ^ 2 := by
  exact weightedLevel_zero (fun d v => (h d v) ^ 2)
end FD1D
