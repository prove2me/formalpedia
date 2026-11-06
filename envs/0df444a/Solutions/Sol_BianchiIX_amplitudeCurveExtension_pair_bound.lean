-- Prove2me | solution 1 for BianchiIX.amplitudeCurveExtension_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:51:59.249901+00:00
-- url     : https://prove2.me/submissions/78dfdf44-81f4-41d0-8c8d-ceafff33c31f

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_amplitudeRootDerivative_bound
import Theorems.Thm_BianchiIX_rootCurveExtension_pair_bound
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


theorem solution {l r θ B : ℝ} (hlr : l ≤ r)
    {U W dU dW : ℝ → ℝ}
    (hU : ∀ x ∈ Icc l r, 0 < U x) (hW : ∀ x ∈ Icc l r, 0 < W x)
    (hdU : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x))
    (hdW : ∀ x ∈ Icc l r, |dW x| ≤ θ * Real.sqrt (W x))
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, U x + W x ≤ B) (x : ℝ) :
    amplitudeCurveExtension l r U dU x + amplitudeCurveExtension l r W dW x ≤
      (25 / 16) * B := by
  apply rootCurveExtension_pair_bound hlr
    (fun y hy => Real.sqrt_pos.mpr (hU y hy)) (fun y hy => Real.sqrt_pos.mpr (hW y hy))
    (fun y hy => amplitudeRootDerivative_bound (hU y hy) (hdU y hy))
    (fun y hy => amplitudeRootDerivative_bound (hW y hy) (hdW y hy)) hθ
  intro y hy
  simpa only [Real.sq_sqrt (hU y hy).le, Real.sq_sqrt (hW y hy).le] using hB y hy
