-- Prove2me | solution 1 for BianchiIX.hasDerivWithinAt_amplitudeRoot
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:33:29.129349+00:00
-- url     : https://prove2.me/submissions/d807cda6-f9a0-4c68-a3a2-c7e5ca7ed0d7

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


theorem solution {U dU : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hpos : 0 < U x) (hU : HasDerivWithinAt U (dU x) s x) :
    HasDerivWithinAt (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU x) s x :=
  hU.sqrt (ne_of_gt hpos)
