-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_amplitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:33:08.480009+00:00
-- url     : https://prove2.me/submissions/88a0c2a0-1378-4dc7-a3b3-056e5250a705

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Theorems.Thm_BianchiIX_coreAuxiliary_amplitude_bounds
import Theorems.Thm_BianchiIX_coreAuxiliary_coefficient_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_coefficient_scales
import Theorems.Thm_BianchiIX_core_clock_quotient_bound
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX


/-- The three amplitude-sensitive radius-row estimates in (B.35). -/
theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let v := y 0 / Real.cosh z
    let w := y 2 / v
    let b := coreWeightedJacobian k z y
    |b 0 0| ≤ 8 * (y 1 + w ^ 2 / k ^ 2) ∧
    |b 0 1 + v / k| ≤ 8 * (y 1 + w) / k ∧
    |b 0 2| ≤ 8 * (y 1 + w / k) / v := by
  intro v w b
  let r := y 0
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨hr5, _, _, _, _, hkr, hk2r2, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr5]
  have hv0 : 0 < v := by dsimp [v]; linarith only [hv]
  have hu0 := hu.1
  have hw0 : 0 ≤ w := hw.1
  have hd : 999 / 1000 ≤ q 1 := (coreAuxiliary_coefficient_bounds hk hr hv hu hw).2.2.2.1
  have hd0 : 0 < q 1 := by linarith only [hd]
  obtain ⟨hR, hU, hP, hpR, hpU, hpP⟩ := coreAuxiliary_amplitude_bounds hk hr hv hu hw
  change |h 3 0| ≤ 2 * y 1 + 3 * w ^ 2 / r ^ 2 at hR
  change |h 3 1 + v - v * (1 - q 1)| ≤ 4 * (y 1 + w) at hU
  change |v * h 3 2| ≤ 2 * (y 1 + w / r) at hP
  change |q 3 * h 1 0| ≤ (y 1 + w ^ 2 / r ^ 2) / 10 at hpR
  change |q 3 * h 1 1| ≤ (y 1 + w / r) / 10 at hpU
  change |v * q 3 * h 1 2| ≤ (y 1 + w / r) / 10 at hpP
  have hwscale : w / r ≤ (3 / 2) * (w / k) := by
    calc
      _ = (k / r) * (w / k) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hkr (by positivity)
  have hw2scale : w ^ 2 / r ^ 2 ≤ (3 / 2) * (w ^ 2 / k ^ 2) := by
    calc
      _ = (k ^ 2 / r ^ 2) * (w ^ 2 / k ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hk2r2 (by positivity)
  have hwk : 0 ≤ w / k := div_nonneg hw0 hk0.le
  have hw2k : 0 ≤ w ^ 2 / k ^ 2 := by positivity
  constructor
  · change |h 3 0 / q 1 - q 3 * h 1 0 / q 1 ^ 2| ≤ 8 * (y 1 + w ^ 2 / k ^ 2)
    have H := core_clock_quotient_bound hd hR hpR
    rw [show 3 * w ^ 2 / r ^ 2 = 3 * (w ^ 2 / r ^ 2) by ring] at H
    linarith only [H, hw2scale, hu0, hw2k]
  constructor
  · have hid : b 0 1 + v / k =
        ((h 3 1 + v - v * (1 - q 1)) / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k := by
      change (h 3 1 / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k + v / k = _
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hk0]
    apply div_le_div_of_nonneg_right _ hk0.le
    have hwr : w / r ≤ w := div_le_self hw0 (by linarith only [hr5])
    have hpU' : |q 3 * h 1 1| ≤ (y 1 + w) / 10 := by linarith only [hpU, hwr]
    have H := core_clock_quotient_bound hd hU hpU'
    linarith only [H, hu0, hw0]
  · have hid : b 0 2 = ((v * h 3 2) / q 1 - (v * q 3 * h 1 2) / q 1 ^ 2) / v := by
      change h 3 2 / q 1 - q 3 * h 1 2 / q 1 ^ 2 = _
      field_simp
    rw [hid, abs_div, abs_of_pos hv0]
    apply div_le_div_of_nonneg_right _ hv0.le
    have H := core_clock_quotient_bound hd hP hpP
    linarith only [H, hwscale, hu0, hwk]
