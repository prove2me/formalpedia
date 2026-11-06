-- Prove2me | solution 1 for BianchiIX.exists_core_cone_threshold
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:27:49.873855+00:00
-- url     : https://prove2.me/submissions/033f2fa1-e2c5-4b4e-b2d7-eb240afeee00

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {R A B : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ 7 * R * Real.sqrt ε ≤ 1 / 32 ∧
      38400 * A * Real.sqrt ε ≤ 1 / 32 ∧ 3 * B * Real.sqrt ε ≤ 1 / 32 := by
  let C := 1 + 7 * R + 38400 * A + 3 * B
  have hC : 0 < C := by dsimp [C]; positivity
  let d := min (1 / 100 : ℝ) (1 / (32 * C))
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hdsq : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd.le
  have hdC : C * d ≤ 1 / 32 := by
    have H := (le_div_iff₀ (show 0 < 32 * C by positivity)).mp (min_le_right (1 / 100) (1 / (32 * C)))
    change d * (32 * C) ≤ 1 at H
    linarith only [H]
  have hbound (X : ℝ) (hX : X ≤ C) : X * Real.sqrt (d ^ 2) ≤ 1 / 32 := by
    rw [hdsq]
    exact (mul_le_mul_of_nonneg_right hX hd.le).trans hdC
  refine ⟨d ^ 2, sq_pos_of_pos hd, ?_, hbound _ ?_, hbound _ ?_, hbound _ ?_⟩
  · have H : d ≤ 1 / 100 := min_le_left _ _
    nlinarith only [H, hd, mul_nonneg hd.le (sub_nonneg.mpr H)]
  all_goals dsimp [C]; linarith only [hR, hA, hB]
