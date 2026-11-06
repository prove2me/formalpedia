-- Prove2me | solution 1 for BianchiIX.rootExtension_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:36:25.836052+00:00
-- url     : https://prove2.me/submissions/130dbf74-b79e-42fb-901e-1b878ae9e8b5

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_rootCutoff_bounds
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


theorem solution {s d e x θ : ℝ} (hs : 0 < s)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) : |d * rootCutoff (e * x / s)| ≤ θ / 2 := by
  have hc := rootCutoff_bounds (div_nonneg hx hs.le)
  rw [abs_mul, abs_of_nonneg hc.1]
  exact (mul_le_of_le_one_right (abs_nonneg d) hc.2).trans hd
