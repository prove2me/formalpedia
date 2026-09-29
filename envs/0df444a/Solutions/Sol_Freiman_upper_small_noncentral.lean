-- Prove2me | solution 1 for Freiman.upper_small_noncentral
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:37:54.526271+00:00
-- url     : https://prove2.me/submissions/59247c3b-8510-4ae5-a7d0-3ede2a3a7a30

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_small_inward
import Theorems.Thm_Freiman_upper_small_outward
import Theorems.Thm_Freiman_upper_small_low_digits
import Theorems.Thm_Freiman_upper_small_constants
import Theorems.Thm_Freiman_upper_local_sides
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3) (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0) :
    localValue (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i ≤ upperSmallBound := by
  by_cases h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) = 4
  · have hI := upper_small_inward l r hl hl0 hr hr0 j i hi h4
    have hO := upper_small_outward l r hl hl0 hr hr0 j i hi h4
    have hv := upper_local_sides (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i
    rw [h4] at hv
    norm_num at hv
    dsimp only [upperSmallBound]
    linarith
  · exact (upper_small_low_digits l r hl hl0 hr hr0 j i hi h4).le.trans
      upper_small_constants.1.le
