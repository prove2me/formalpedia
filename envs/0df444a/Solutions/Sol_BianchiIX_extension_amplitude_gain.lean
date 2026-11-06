-- Prove2me | solution 1 for BianchiIX.extension_amplitude_gain
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:38:11.931285+00:00
-- url     : https://prove2.me/submissions/7dd3a67e-38d1-44ff-aedf-f1bd867530b1

import Theorems.Thm_BianchiIX_rpow_gain_bound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {B Bmax C : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hC : 0 ≤ C) (hbudget : (25 / 16 : ℝ) * C * Bmax ^ (17 / 30 : ℝ) ≤ 1) :
    (25 / 16 : ℝ) * (C * B ^ (19 / 10 : ℝ)) ≤ B ^ (4 / 3 : ℝ) := by
  have H := rpow_gain_bound (C := (25 / 16 : ℝ) * C)
    (p := 19 / 10) (q := 4 / 3) hB hmax (by positivity) (by norm_num)
    (by norm_num; exact hbudget)
  simpa only [mul_assoc] using H
