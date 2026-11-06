-- Prove2me | solution 1 for BianchiIX.measurable_curveSampleStep
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:32:02.865371+00:00
-- url     : https://prove2.me/submissions/99d6d575-6d41-4042-8966-6417db0c9ea4

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


theorem solution {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} (hl : Measurable l) (hr : Measurable r) (hx : Measurable x) (n : ℕ) :
    Measurable (fun q => curveSampleStep (l q) (r q) (x q) n) :=
  (Measurable.ite (measurableSet_lt hx hr) (hr.sub hx) (hl.sub hx)).div_const _
