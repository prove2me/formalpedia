-- Prove2me | solution 1 for Freiman.gap_leaf_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:18.612002+00:00
-- url     : https://prove2.me/submissions/88510b86-d6b5-4f0e-a3e8-7cf009f3f483

import Definitions.Def_Freiman_gapCertificateData
import Theorems.Thm_Freiman_gap_leaf_above_soundness
import Theorems.Thm_Freiman_gap_leaf_below_soundness
import Theorems.Thm_Freiman_gap_leaf_prior_soundness
import Theorems.Thm_Freiman_gap_leaf_upperRow_soundness
import Theorems.Thm_Freiman_gap_leaf_terminal_soundness

open Freiman

theorem solution (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (r : GapReason) (hcheck : gapLeafCheck lower upper mode s r) : gapModeOutcome mode a i := by
  cases r with
  | above j => exact gap_leaf_above_soundness lower upper mode s a i hd hc hl hu hm j hcheck
  | below => exact gap_leaf_below_soundness lower upper mode s a i hd hc hl hu hm hcheck
  | prior n => exact gap_leaf_prior_soundness lower upper mode s a i hd hc hl hu hm n hcheck
  | upperRow n => exact gap_leaf_upperRow_soundness lower upper mode s a i hd hc hl hu hm n hcheck
  | terminal => exact gap_leaf_terminal_soundness lower upper mode s a i hd hc hl hu hm hcheck
