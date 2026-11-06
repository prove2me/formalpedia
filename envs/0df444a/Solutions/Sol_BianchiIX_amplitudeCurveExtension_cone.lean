-- Prove2me | solution 1 for BianchiIX.amplitudeCurveExtension_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:51:06.788196+00:00
-- url     : https://prove2.me/submissions/1d66be41-1bb3-4614-8095-5159d2f14d00

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_amplitudeRootDerivative_bound
import Theorems.Thm_BianchiIX_hasDerivWithinAt_amplitudeRoot
import Theorems.Thm_BianchiIX_rootCurveExtension_square_cone
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


theorem solution {l r θ : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hU : ∀ x ∈ Icc l r, HasDerivWithinAt U (dU x) (Icc l r) x)
    (hcone : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x)) (hθ : θ ≤ 1) (x : ℝ) :
    |deriv (amplitudeCurveExtension l r U dU) x| ≤
      θ * Real.sqrt (amplitudeCurveExtension l r U dU x) :=
  rootCurveExtension_square_cone hlr (fun y hy => Real.sqrt_pos.mpr (hpos y hy))
    (fun y hy => amplitudeRootDerivative_bound (hpos y hy) (hcone y hy)) hθ
    (fun y hy => hasDerivWithinAt_amplitudeRoot (hpos y hy) (hU y hy)) x
