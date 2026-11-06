-- Prove2me | solution 1 for BianchiIX.coreAngle_radius_drift_shifted
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:41:41.150847+00:00
-- url     : https://prove2.me/submissions/a2812227-4904-4edb-a456-eba8eabc9806

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreAngle_radius_drift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- The bound is unchanged when the constructed angle clock is based at zero. -/
theorem solution {Y : ℝ → CoreAngleState} {a b k z₀ : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z)
    (hinit : Y a 0 = k) (hentry : Real.cosh (a + z₀) = k)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh (z + z₀))
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ (1 / 10000) / k) :
    |Y b 0 - k| ≤ 16 / k * (Y a 1 + (Y a 2) ^ 2) := by
  have hmem (z : ℝ) (hz : z ∈ Icc (a + z₀) (b + z₀)) : z - z₀ ∈ Icc a b := by
    constructor <;> linarith [hz.1, hz.2]
  have hsol (z : ℝ) (hz : z ∈ Icc (a + z₀) (b + z₀)) :
      HasDerivAt (fun u => Y (u - z₀)) (coreAngleField z (Y (z - z₀))) z := by
    have H := (hY (z - z₀) (hmem z hz)).scomp z ((hasDerivAt_id z).sub_const z₀)
    simp only [sub_add_cancel, one_smul] at H
    convert! H using 1
  have H := coreAngle_radius_drift (Y := fun z => Y (z - z₀)) (by linarith : a + z₀ ≤ b + z₀) hk hsol
    (by simpa only [add_sub_cancel_right] using hinit) hentry
    (fun z hz => hr _ (hmem z hz))
    (fun z hz => by simpa only [sub_add_cancel] using hv _ (hmem z hz))
    (fun z hz => hu _ (hmem z hz)) (fun z hz => hp _ (hmem z hz))
  simpa only [add_sub_cancel_right] using H
