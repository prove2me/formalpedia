-- Prove2me | solution 1 for Freiman.gap_extremizer_A_noncentral
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:53.211048+00:00
-- url     : https://prove2.me/submissions/6691b4c2-82a2-4eb7-bae4-d52b9d34dc64

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_extremizer_A_window_coverage
import Theorems.Thm_Freiman_gap_extremizer_A_window_checks
import Theorems.Thm_Freiman_gap_extremizer_A_data
import Theorems.Thm_Freiman_gap_window_upper

open Freiman

theorem solution (i : ℤ) (hi : i ≠ 0) : localValue gapExtremizerA i < 22639/5000 := by
  obtain ⟨j,hj,heq⟩ := gap_extremizer_A_window_coverage i hi
  have h := gap_window_upper gapExtremizerA i 5 gap_extremizer_A_data.1
  rw [heq] at h
  have hn : (gapCylinderUpper (gapLocalWindow gapExtremizerA j 5) 5 : ℝ) < 22639/5000 := by
    have hcast : (gapCylinderUpper (gapLocalWindow gapExtremizerA j 5) 5 : ℝ) < ((22639/5000 : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).mpr (gap_extremizer_A_window_checks j hj)
    norm_num at hcast
    exact hcast
  exact lt_trans h hn
