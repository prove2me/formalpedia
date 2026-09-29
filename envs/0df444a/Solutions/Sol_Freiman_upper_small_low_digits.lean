-- Prove2me | solution 1 for Freiman.upper_small_low_digits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:17:55.955154+00:00
-- url     : https://prove2.me/submissions/b5db2d59-1f7b-46e0-a2e3-702f678eb1f3

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_cf_convergence

open Freiman
set_option autoImplicit false

private theorem one_bound (b : ℕ → ℕ+) (hb : upperAdmissible b) (k : ℕ) :
    (upperOne b k : ℕ) ≤ 4 := by
  cases k with
  | zero => norm_num [upperOne]
  | succ k => exact hb.1 k

theorem solution (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3)
    (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) (j : ℕ) (i : ℤ) (hi : i ≠ 0)
    (h4 : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) ≠ 4) :
    localValue (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j) i < 5 := by
  have hb : (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) ≤ 4 := by
    unfold upperPad
    split_ifs with hpad
    · unfold upperCentral
      split_ifs with hz hp
      · exact le_rfl
      · exact one_bound r hr _
      · exact one_bound l hl _
    · norm_num
  have hd : ((upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) : ℝ) ≤ 3 := by
    exact_mod_cast (show (upperPad (upperCentral 4 (upperOne l) (upperOne r)) j i : ℕ) ≤ 3 by omega)
  have hlv := (cf_convergence (fun n : ℕ =>
    upperPad (upperCentral 4 (upperOne l) (upperOne r)) j (i - (n : ℤ) - 1))).2.2.2.1
  have hrv := (cf_convergence (fun n : ℕ =>
    upperPad (upperCentral 4 (upperOne l) (upperOne r)) j (i + (n : ℤ) + 1))).2.2.2.1
  unfold localValue
  linarith
