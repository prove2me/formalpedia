-- Prove2me | solution 1 for FD1D.LocalHazard.b_eq_neg_two_mul_a_mul_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:48.666925+00:00
-- url     : https://prove2.me/submissions/688dc49b-39b3-4fb2-898f-a37ec47660b2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_b_eq_neg_a_mul_hazardDiff
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y = -2 * a * w a h x y := by
  rw [b_eq_neg_a_mul_hazardDiff ha]
  simp only [w]
  ring
end FD1D.LocalHazard
