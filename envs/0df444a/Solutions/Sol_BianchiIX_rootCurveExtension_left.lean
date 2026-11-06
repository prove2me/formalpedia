-- Prove2me | solution 1 for BianchiIX.rootCurveExtension_left
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:36:40.725412+00:00
-- url     : https://prove2.me/submissions/a4d39923-85b3-45a0-9b6a-c8abb93dc34c

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


theorem solution {l r x : ℝ} (f df : ℝ → ℝ) (hlr : l ≤ r) (hx : x ≤ l) :
    rootCurveExtension l r f df x = rootExtension (f l) (df l) (-1) (x - l) ∧
      rootCurveDerivative l r f df x = df l * rootCutoff (-(x - l) / f l) := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · simp [rootCurveExtension, rootCurveDerivative, hx]
  · simp [rootCurveExtension, rootCurveDerivative, not_lt_of_ge hlr, rootExtension_zero, rootCutoff]
