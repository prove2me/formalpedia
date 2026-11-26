-- Prove2me | solution 1 for FD1D.LocalHazard.hR_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:57.509875+00:00
-- url     : https://prove2.me/submissions/87cdc539-f01a-4230-ada9-fd8c54d06658

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
    0 < hR a h x y := by
  by_cases hne : x + y = 0
  · simp [hR, hne, hh]
  · have hN := N_pos hne
    have hD := D_pos ha hne
    have hxa := count_add_a_pos ha x
    simp only [hR, if_neg hne]
    positivity
end FD1D.LocalHazard
