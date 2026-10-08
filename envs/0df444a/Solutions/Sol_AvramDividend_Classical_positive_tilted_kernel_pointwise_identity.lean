-- Prove2me | solution 1 for AvramDividend.Classical.positive_tilted_kernel_pointwise_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:47:05.336977+00:00
-- url     : https://prove2.me/submissions/b561c973-0dbc-420a-b24f-e48b62be403a

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem solution (a s z : ℝ) (ha : 0 ≤ a) (hs : 0 < s) (hz : 0 ≤ z) :
    ENNReal.ofReal ((1 - Real.exp (-s * z)) / s) +
        ENNReal.ofReal (1 / s) *
          (ENNReal.ofReal (Real.exp (-s * z)) *
            ENNReal.ofReal (1 - Real.exp (-a * z))) =
      ENNReal.ofReal ((1 - Real.exp (-(s + a) * z)) / s) := by
  have hsz : -s * z ≤ 0 := by
    nlinarith
  have haz : -a * z ≤ 0 := by
    nlinarith
  have htail : 0 ≤ 1 - Real.exp (-s * z) := by
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr hsz
  have hweight : 0 ≤ 1 - Real.exp (-a * z) := by
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr haz
  have hinv : 0 ≤ 1 / s := (one_div_pos.mpr hs).le
  have hexp : 0 ≤ Real.exp (-s * z) := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hexp]
  rw [← ENNReal.ofReal_mul hinv]
  rw [← ENNReal.ofReal_add (div_nonneg htail hs.le)
    (mul_nonneg hinv (mul_nonneg hexp hweight))]
  apply congrArg ENNReal.ofReal
  rw [show Real.exp (-(s + a) * z) =
      Real.exp (-s * z) * Real.exp (-a * z) by
        rw [← Real.exp_add]
        congr 1
        ring]
  field_simp [hs.ne']
  ring
