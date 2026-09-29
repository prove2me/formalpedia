-- Prove2me | solution 1 for Freiman.gap_minimum_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:54.108399+00:00
-- url     : https://prove2.me/submissions/8046749c-1559-4fb1-a848-ce15e1db3853

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_minimum_left_tail
import Theorems.Thm_Freiman_gap_minimum_right_tail
import Theorems.Thm_Freiman_gap_capped_digits
import Theorems.Thm_Freiman_gap_seed_centre
import Theorems.Thm_Freiman_gap_endpoint_B_value
import Theorems.Thm_Freiman_gap_join_centre
import Theorems.Thm_Freiman_gap_minimum_forbidden

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedB) : localValue a 0 ≥ cF := by
  have hd := gap_capped_digits a hc
  have ha := gap_minimum_forbidden a hc
  have hl := gap_minimum_left_tail a hd ha hs
  have hr := gap_minimum_right_tail a hd ha hs
  have h0 := gap_seed_centre a (Or.inr hs)
  have he := gap_endpoint_B_value
  rw [gapExtremizerB,gap_join_centre] at he
  linarith
