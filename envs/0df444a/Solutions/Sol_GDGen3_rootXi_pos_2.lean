-- Prove2me | solution 2 for GDGen3.rootXi_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:39:53.29692+00:00
-- url     : https://prove2.me/submissions/031a48ee-d292-4995-a5ba-9b5c25edcdb6

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_X_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : i ≠ 0) :
    0 < rootXi r N i := by
  unfold rootXi
  rw [if_neg hi]
  by_cases hiN : i < N
  · rw [if_pos hiN]
    have hx := X_pos r hr hr1 N i (by omega) hiN
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hdisc : (1 + C r N i) ^ 2 < (1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1) := by
      have hd : 0 < 4 * X r N i / pj r (i + 1) := div_pos (by positivity) hp
      linarith
    have hsq : |1 + C r N i| < Real.sqrt ((1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1)) := by
      rw [← Real.sqrt_sq_eq_abs (1 + C r N i)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hdisc
    have hb := le_abs_self (1 + C r N i)
    linarith
  · simp [hiN]
