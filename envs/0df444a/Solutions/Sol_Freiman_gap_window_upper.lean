-- Prove2me | solution 1 for Freiman.gap_window_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:53.08941+00:00
-- url     : https://prove2.me/submissions/f713560d-ab7f-4473-81ee-57d827225792

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_window_match
import Theorems.Thm_Freiman_gap_cylinder_semantics

open Freiman

theorem solution (a : ℤ → ℕ+) (i : ℤ) (r : ℕ) (hd : gapDigits a) : localValue a i < (gapCylinderUpper (gapLocalWindow a i r) r : ℝ) := by
  have hm := gap_window_match a i r
  have h := (gap_cylinder_semantics a i ⟨gapLocalWindow a i r,r⟩ r hd hm hm.1).2
  simpa only [add_sub_cancel_right] using h
