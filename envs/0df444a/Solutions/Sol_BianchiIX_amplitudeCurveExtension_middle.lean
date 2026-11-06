-- Prove2me | solution 1 for BianchiIX.amplitudeCurveExtension_middle
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:37:31.557063+00:00
-- url     : https://prove2.me/submissions/ded729fc-e6e6-488c-b29b-3ba175cb3450

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_rootCurveExtension_middle
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX
open Set


theorem solution {l r x : ℝ} {U dU : ℝ → ℝ}
    (hx : x ∈ Icc l r) (hpos : 0 ≤ U x) :
    amplitudeCurveExtension l r U dU x = U x := by
  rw [amplitudeCurveExtension, (rootCurveExtension_middle _ _ hx).1, Real.sq_sqrt hpos]
