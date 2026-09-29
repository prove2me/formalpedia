-- Prove2me | solution 1 for Freiman.gap_extremizer_B_noncentral
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:05.790925+00:00
-- url     : https://prove2.me/submissions/630092ab-03ec-4434-987f-efa8820fcc0b

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_extremizer_B_window_coverage
import Theorems.Thm_Freiman_gap_extremizer_B_window_checks
import Theorems.Thm_Freiman_gap_extremizer_B_data
import Theorems.Thm_Freiman_gap_window_upper

open Freiman

theorem solution (i : ℤ) (hi : i ≠ 0) : localValue gapExtremizerB i < 22639/5000 := by
  obtain ⟨j,hj,heq⟩ := gap_extremizer_B_window_coverage i hi
  have h := gap_window_upper gapExtremizerB i 4 gap_extremizer_B_data.1
  rw [heq] at h
  have hn : (gapCylinderUpper (gapLocalWindow gapExtremizerB j 4) 4 : ℝ) < 22639/5000 := by
    have hcast : (gapCylinderUpper (gapLocalWindow gapExtremizerB j 4) 4 : ℝ) < ((22639/5000 : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).mpr (gap_extremizer_B_window_checks j hj)
    norm_num at hcast
    exact hcast
  exact lt_trans h hn
