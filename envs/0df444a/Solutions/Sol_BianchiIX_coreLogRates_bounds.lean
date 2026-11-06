-- Prove2me | solution 1 for BianchiIX.coreLogRates_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:31:31.787837+00:00
-- url     : https://prove2.me/submissions/a498e3f2-0521-4a0b-bb09-a67d73940b17

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Theorems.Thm_BianchiIX_coreAuxiliary_coefficient_bounds
import Theorems.Thm_BianchiIX_core_log_quotient_bound
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

noncomputable section
open BianchiIX


theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    |coreLogRates z y 0| ≤ 2 * k ∧ |coreLogRates z y 1| ≤ 4 / k := by
  let r := y 0
  let q := coreAuxiliary z y
  have hk0 : 0 < k := by linarith only [hk]
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr.1, hk]
  obtain ⟨hC, ha, _, hd, _⟩ := coreAuxiliary_coefficient_bounds hk hr hv hu hw
  change 0 ≤ q 0 ∧ q 0 ≤ 1 / 100 at hC
  change |q 2| ≤ r at ha
  change 999 / 1000 ≤ q 1 at hd
  have hz : |(0 : ℝ)| ≤ 0 := by norm_num
  constructor
  · have H := core_log_quotient_bound hd ha hz
    simp only [zero_div, sub_zero, add_zero] at H
    change |q 2 / q 1| ≤ 2 * k
    exact H.trans (by dsimp [r]; linarith only [hr.2, hk])
  · have hnum : |-2 * (1 + q 0) / r| ≤ 2 * (1 + q 0) / r := by
      rw [abs_div, abs_mul, abs_of_pos hr0, abs_of_nonneg (by linarith only [hC.1] : 0 ≤ 1 + q 0)]
      norm_num
    have H := core_log_quotient_bound hd hnum hz
    simp only [zero_div, sub_zero, add_zero] at H
    have heq : coreLogRates z y 1 = (-2 * (1 + q 0) / r) / q 1 := by
      change -2 * (1 + q 0) / (r * q 1) = _
      ring
    rw [heq]
    calc
      _ ≤ 11 / 10 * (2 * (1 + q 0) / r) := H
      _ = ((11 / 5) * (1 + q 0)) / r := by ring
      _ ≤ (5 / 2) / r := div_le_div_of_nonneg_right (by linarith only [hC.2]) hr0.le
      _ ≤ 4 / k := by
        apply (div_le_div_iff₀ hr0 hk0).mpr
        dsimp [r]
        linarith only [hr.1, hk]
