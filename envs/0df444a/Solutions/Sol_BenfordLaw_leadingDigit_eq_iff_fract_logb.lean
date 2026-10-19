-- Prove2me | solution 1 for BenfordLaw.leadingDigit_eq_iff_fract_logb
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:43:31.353765+00:00
-- url     : https://prove2.me/submissions/1158225f-ec75-43ee-8f5e-f05178610626

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

theorem solution (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : 0 < x)
    (d : ℕ) (hd1 : 1 ≤ d) (hdb : d < b) :
    leadingDigit b x = d ↔
      Real.logb b d ≤ Int.fract (Real.logb b x) ∧
        Int.fract (Real.logb b x) < Real.logb b (d + 1) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold leadingDigit
  rw [Nat.floor_eq_iff (by positivity), Real.logb_le_iff_le_rpow hb1 hd0,
    Real.lt_logb_iff_rpow_lt hb1 (by positivity)]
