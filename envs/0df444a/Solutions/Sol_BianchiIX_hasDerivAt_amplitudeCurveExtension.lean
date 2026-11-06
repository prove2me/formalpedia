-- Prove2me | solution 1 for BianchiIX.hasDerivAt_amplitudeCurveExtension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:44:39.447728+00:00
-- url     : https://prove2.me/submissions/6830b615-6226-4627-a9ef-b3cc7e6f1ce7

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_hasDerivAt_rootCurveExtension
import Theorems.Thm_BianchiIX_hasDerivWithinAt_amplitudeRoot
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


theorem solution {l r : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hU : ∀ x ∈ Icc l r, HasDerivWithinAt U (dU x) (Icc l r) x) (x : ℝ) :
    HasDerivAt (amplitudeCurveExtension l r U dU)
      (2 * rootCurveExtension l r (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU) x *
        rootCurveDerivative l r (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU) x) x := by
  have H := hasDerivAt_rootCurveExtension (f := fun y => Real.sqrt (U y))
    (df := amplitudeRootDerivative U dU) hlr
    (Real.sqrt_pos.mpr (hpos l ⟨le_rfl, hlr.le⟩))
    (Real.sqrt_pos.mpr (hpos r ⟨hlr.le, le_rfl⟩))
    (fun y hy => hasDerivWithinAt_amplitudeRoot (hpos y hy) (hU y hy)) x
  convert! H.pow 2 using 1
  simp
