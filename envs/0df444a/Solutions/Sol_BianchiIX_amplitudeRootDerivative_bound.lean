-- Prove2me | solution 1 for BianchiIX.amplitudeRootDerivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:33:54.967216+00:00
-- url     : https://prove2.me/submissions/2a583e3b-de4c-48f5-8789-b320d40bb5f7

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


theorem solution {U dU : ℝ → ℝ} {x θ : ℝ}
    (hpos : 0 < U x) (hcone : |dU x| ≤ θ * Real.sqrt (U x)) :
    |amplitudeRootDerivative U dU x| ≤ θ / 2 := by
  have hs : 0 < Real.sqrt (U x) := Real.sqrt_pos.mpr hpos
  rw [amplitudeRootDerivative, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (U x))]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (U x))).mpr
  nlinarith
