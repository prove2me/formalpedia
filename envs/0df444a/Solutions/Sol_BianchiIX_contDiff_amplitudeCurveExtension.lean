-- Prove2me | solution 1 for BianchiIX.contDiff_amplitudeCurveExtension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:46:00.778798+00:00
-- url     : https://prove2.me/submissions/19a89b89-c4da-4343-8998-c7a99ac0466f

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_contDiff_rootCurveExtension
import Theorems.Thm_BianchiIX_continuousOn_amplitudeRootDerivative
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
    (hU : ∀ x ∈ Icc l r, HasDerivWithinAt U (dU x) (Icc l r) x)
    (hdU : ContinuousOn dU (Icc l r)) : ContDiff ℝ 1 (amplitudeCurveExtension l r U dU) := by
  exact (contDiff_rootCurveExtension (f := fun y => Real.sqrt (U y))
    (df := amplitudeRootDerivative U dU) hlr
    (Real.sqrt_pos.mpr (hpos l ⟨le_rfl, hlr.le⟩))
    (Real.sqrt_pos.mpr (hpos r ⟨hlr.le, le_rfl⟩))
    (fun x hx => hasDerivWithinAt_amplitudeRoot (hpos x hx) (hU x hx))
    (continuousOn_amplitudeRootDerivative hpos (fun x hx => (hU x hx).continuousWithinAt) hdU)).pow 2
