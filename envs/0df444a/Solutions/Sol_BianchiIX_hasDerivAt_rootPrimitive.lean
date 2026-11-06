-- Prove2me | solution 1 for BianchiIX.hasDerivAt_rootPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:34:40.365067+00:00
-- url     : https://prove2.me/submissions/f7c8fd45-fa3e-429e-a1e7-88673810bc8d

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_continuous_rootCutoff
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


theorem solution (t : ℝ) : HasDerivAt rootPrimitive (rootCutoff t) t :=
  intervalIntegral.integral_hasDerivAt_right (continuous_rootCutoff.intervalIntegrable _ _)
    continuous_rootCutoff.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_rootCutoff.continuousAt
