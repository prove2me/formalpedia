-- Prove2me | solution 1 for BianchiIX.square_derivative_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:29:54.227196+00:00
-- url     : https://prove2.me/submissions/3cc2b551-c7b4-4313-ab23-f269b236db60

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {f : ℝ → ℝ} {d x θ : ℝ} (hf : HasDerivAt f d x)
    (hpos : 0 < f x) (hd : |d| ≤ θ / 2) :
    |deriv (fun z => f z ^ 2) x| ≤ θ * Real.sqrt (f x ^ 2) := by
  have hp' : HasDerivAt (fun z => f z ^ 2) (2 * f x * d) x := by
    convert! hf.pow 2 using 1
    simp
  rw [hp'.deriv, Real.sqrt_sq hpos.le]
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * f x * (θ / 2) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring
