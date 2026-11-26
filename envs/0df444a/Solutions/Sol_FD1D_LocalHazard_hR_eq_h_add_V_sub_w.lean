-- Prove2me | solution 1 for FD1D.LocalHazard.hR_eq_h_add_V_sub_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:36.27444+00:00
-- url     : https://prove2.me/submissions/3587ea9e-f4fd-4c70-b483-d0ed42642d4c

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution (a h : ℝ) (x y : ℕ) :
    hR a h x y = h + V a h x y - w a h x y := by
  simp only [V, w]
  ring
end FD1D.LocalHazard
