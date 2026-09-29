-- Prove2me | solution 1 for Freiman.gap_maximum_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:53.998229+00:00
-- url     : https://prove2.me/submissions/71a918d0-ea9e-4193-a98f-295aca3850ff

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_maximum_left_tail
import Theorems.Thm_Freiman_gap_maximum_right_tail
import Theorems.Thm_Freiman_gap_capped_digits
import Theorems.Thm_Freiman_gap_seed_centre
import Theorems.Thm_Freiman_gap_endpoint_A_value
import Theorems.Thm_Freiman_gap_join_centre
import Theorems.Thm_Freiman_gap_maximum_admissible

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) (hs : gapMatch a 0 gapSeedA) : localValue a 0 ≤ gapLeft := by
  have hd := gap_capped_digits a hc
  have ha := gap_maximum_admissible a hc
  have hl := gap_maximum_left_tail a hd ha hs
  have hr := gap_maximum_right_tail a hd ha hs
  have h0 := gap_seed_centre a (Or.inl hs)
  have he := gap_endpoint_A_value
  rw [gapExtremizerA,gap_join_centre] at he
  linarith
