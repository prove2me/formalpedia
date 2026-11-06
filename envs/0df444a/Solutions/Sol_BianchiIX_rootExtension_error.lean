-- Prove2me | solution 1 for BianchiIX.rootExtension_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:42:41.229989+00:00
-- url     : https://prove2.me/submissions/42db7d3a-1f45-4775-aefa-ecef294a2ce4

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_rootPrimitive_bounds
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


theorem solution {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) :
    |rootExtension s d e x - s| ≤ θ * s / 4 := by
  have hp := rootPrimitive_bounds (div_nonneg hx hs.le)
  rw [rootExtension, add_sub_cancel_left, abs_mul, abs_mul, abs_mul,
    he, one_mul, abs_of_pos hs, abs_of_nonneg hp.1]
  calc
    _ ≤ |d| * s * (1 / 2) := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg (abs_nonneg d) hs.le)
    _ ≤ (θ / 2) * s * (1 / 2) := by gcongr
    _ = _ := by ring
