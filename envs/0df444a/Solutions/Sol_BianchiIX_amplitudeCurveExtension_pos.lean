-- Prove2me | solution 1 for BianchiIX.amplitudeCurveExtension_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:49:59.74428+00:00
-- url     : https://prove2.me/submissions/2af87352-8b14-4e08-8d22-2a12a4c22a1a

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_amplitudeRootDerivative_bound
import Theorems.Thm_BianchiIX_rootCurveExtension_pos
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


theorem solution {l r θ : ℝ} (hlr : l ≤ r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hcone : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x)) (hθ : θ ≤ 1) (x : ℝ) :
    0 < amplitudeCurveExtension l r U dU x :=
  pow_pos (rootCurveExtension_pos hlr (fun y hy => Real.sqrt_pos.mpr (hpos y hy))
    (fun y hy => amplitudeRootDerivative_bound (hpos y hy) (hcone y hy)) hθ x) 2
