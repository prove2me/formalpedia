-- Prove2me | solution 1 for BianchiIX.rootCurveExtension_right
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:37:05.770249+00:00
-- url     : https://prove2.me/submissions/1eb47159-ad61-4ff3-b223-887e57457175

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_rootExtension_zero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {l r x : ℝ} (f df : ℝ → ℝ) (hlr : l ≤ r) (hx : r ≤ x) :
    rootCurveExtension l r f df x = rootExtension (f r) (df r) 1 (x - r) ∧
      rootCurveDerivative l r f df x = df r * rootCutoff ((x - r) / f r) := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · simp [rootCurveExtension, rootCurveDerivative, hx, not_lt_of_ge (hlr.trans hx.le)]
  · simp [rootCurveExtension, rootCurveDerivative, not_lt_of_ge hlr, rootExtension_zero, rootCutoff]
