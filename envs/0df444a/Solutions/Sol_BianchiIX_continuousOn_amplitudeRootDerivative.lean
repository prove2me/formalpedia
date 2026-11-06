-- Prove2me | solution 1 for BianchiIX.continuousOn_amplitudeRootDerivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:34:20.155811+00:00
-- url     : https://prove2.me/submissions/abb1ce93-52ac-4ddf-b8f3-35688663206e

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
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


theorem solution {U dU : ℝ → ℝ} {s : Set ℝ}
    (hpos : ∀ x ∈ s, 0 < U x) (hU : ContinuousOn U s) (hdU : ContinuousOn dU s) :
    ContinuousOn (amplitudeRootDerivative U dU) s :=
  hdU.div (continuousOn_const.mul hU.sqrt)
    (fun x hx => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hpos x hx))))
