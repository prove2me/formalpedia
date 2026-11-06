-- Prove2me | solution 1 for BianchiIX.amplitudeCurveExtension_deriv_middle
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:46:38.850239+00:00
-- url     : https://prove2.me/submissions/73c86fbb-a2aa-40ef-a366-73babcc4b0cb

import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Theorems.Thm_BianchiIX_hasDerivAt_amplitudeCurveExtension
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


theorem solution {l r x : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ y ∈ Icc l r, 0 < U y)
    (hU : ∀ y ∈ Icc l r, HasDerivWithinAt U (dU y) (Icc l r) y) (hx : x ∈ Icc l r) :
    deriv (amplitudeCurveExtension l r U dU) x = dU x := by
  rw [(hasDerivAt_amplitudeCurveExtension hlr hpos hU x).deriv,
    (rootCurveExtension_middle _ _ hx).1, (rootCurveExtension_middle _ _ hx).2]
  dsimp only [amplitudeRootDerivative]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (hpos x hx))]
