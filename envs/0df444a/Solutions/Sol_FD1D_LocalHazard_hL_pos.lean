-- Prove2me | solution 1 for FD1D.LocalHazard.hL_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:48.008507+00:00
-- url     : https://prove2.me/submissions/e00e67fe-e6f4-4d95-9ef6-6cb41e73d4cd

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_pos
import Theorems.Thm_FD1D_LocalHazard_count_add_a_pos
import Theorems.Thm_FD1D_LocalHazard_D_pos
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    0 < hL a h x y := by
  by_cases hne : x + y = 0
  · simp [hL, hne, hh]
  · have hN := N_pos hne
    have hD := D_pos ha hne
    have hya := count_add_a_pos ha y
    simp only [hL, if_neg hne]
    positivity
end FD1D.LocalHazard
