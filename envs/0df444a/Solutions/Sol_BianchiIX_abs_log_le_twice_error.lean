-- Prove2me | solution 1 for BianchiIX.abs_log_le_twice_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:21:37.07841+00:00
-- url     : https://prove2.me/submissions/70eb5433-6db6-4e07-98b9-03337b7502a4

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {t e : ℝ} (he : e ≤ 1 / 4) (ht : |t - 1| ≤ e) :
    |Real.log t| ≤ 2 * e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans ht
  have ht0 : 0 < t := by linarith only [(abs_le.mp ht).1, he]
  have hhalf : 1 / 2 ≤ t := by linarith only [(abs_le.mp ht).1, he]
  have Hinv : 1 / t ≤ 1 + 2 * e := (div_le_iff₀ ht0).mpr (by
    nlinarith only [(abs_le.mp ht).1, mul_le_mul_of_nonneg_left hhalf he0])
  have Hlo := Real.one_sub_inv_le_log_of_pos ht0
  rw [inv_eq_one_div] at Hlo
  have Hhi := Real.log_le_sub_one_of_pos ht0
  exact abs_le.mpr ⟨by linarith only [Hlo, Hinv],
    by linarith only [Hhi, (abs_le.mp ht).2, he0]⟩
