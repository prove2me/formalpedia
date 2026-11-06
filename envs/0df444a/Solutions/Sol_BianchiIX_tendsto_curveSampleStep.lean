-- Prove2me | solution 1 for BianchiIX.tendsto_curveSampleStep
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:31:37.482744+00:00
-- url     : https://prove2.me/submissions/d3a1b285-2c81-45da-8f20-a0300dba15cd

import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology


theorem solution (l r x : ℝ) :
    Tendsto (curveSampleStep l r x) atTop (𝓝 0) := by
  have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    ((if x < r then r - x else l - x) / 3)
  unfold curveSampleStep
  simpa only [mul_zero, div_mul_eq_div_div, mul_one_div] using H
