-- Prove2me | solution 1 for FD1D.LocalHazard.hL_eq_h_add_V_add_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:34.512279+00:00
-- url     : https://prove2.me/submissions/4d448abf-6151-4a79-b9f0-4dcf2b3f3a0b

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
    hL a h x y = h + V a h x y + w a h x y := by
  simp only [V, w]
  ring
end FD1D.LocalHazard
