-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_strong_off_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:08:43.524724+00:00
-- url     : https://prove2.me/submissions/29aa3d45-27ac-4a80-9fe2-7518ff04a80c

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
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

noncomputable section
open BianchiIX


theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    |(coreWeightedJacobian k z y) 1 0| ≤ 2 * k * y 1 ∧
    |(coreWeightedJacobian k z y) 1 2| ≤ 4 * y 1 := by
  let r := y 0
  let u := y 1
  let v := r / Real.cosh z
  let m := (1 / 10000) / k
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  obtain ⟨hr5, hm0, hm, _, hmr, hkr, _, _⟩ := coreBootstrap_coefficient_scales hk hr
  obtain ⟨_, ha, _, hd, _, _, hdR, _, hdP, haR, haP, _⟩ :=
    coreAuxiliary_coefficient_bounds hk hr hv hu hw
  change |q 2| ≤ r at ha
  change 999 / 1000 ≤ q 1 at hd
  change |h 1 0| ≤ m / r ^ 2 at hdR
  change |h 1 2| ≤ 2 * m / (v * r ^ 2) at hdP
  change m / r ≤ 1 / 100 at hmr
  change k / r ≤ 3 / 2 at hkr
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hv0 : 0 < v := by dsimp [v, r]; linarith
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < q 1 := by linarith
  have hu0 : 0 ≤ u := hu.1
  have haDR : |q 2 * h 1 0| ≤ 1 / 10 := by
    calc
      _ = |q 2| * |h 1 0| := abs_mul _ _
      _ ≤ r * (m / r ^ 2) := mul_le_mul ha hdR (abs_nonneg _) hr0.le
      _ = m / r := by field_simp
      _ ≤ 1 / 10 := by linarith only [hmr]
  have haDP : |r * q 2 * h 1 2| ≤ 1 / 10 := by
    calc
      _ = r * |q 2| * |h 1 2| := by rw [abs_mul, abs_mul, abs_of_pos hr0]
      _ ≤ r * r * (2 * m / (v * r ^ 2)) := by gcongr
      _ = 2 * m / v := by field_simp
      _ ≤ 1 / 10 := (div_le_iff₀ hv0).mpr (by dsimp [v, r, m]; linarith)
  have hscaledAP : |r * h 2 2| ≤ 1 := by
    rw [abs_mul, abs_of_pos hr0]
    have H := mul_le_mul_of_nonneg_left haP hr0.le
    change r * |h 2 2| ≤ r * (1 / r) at H
    simpa only [mul_one_div_cancel (ne_of_gt hr0)] using H
  constructor
  · have H : |h 2 0 / q 1 - q 2 * h 1 0 / q 1 ^ 2| ≤ 2 :=
      (core_clock_quotient_bound hd haR haDR).trans (by norm_num)
    have hid : (coreWeightedJacobian k z y) 1 0 =
        (k * u) * (h 2 0 / q 1 - q 2 * h 1 0 / q 1 ^ 2) := by
      change k * (u * h 2 0 / q 1 - u * q 2 * h 1 0 / q 1 ^ 2) = _
      ring
    rw [hid, abs_mul, abs_of_nonneg (mul_nonneg hk0.le hu0)]
    have H' := mul_le_mul_of_nonneg_left H (mul_nonneg hk0.le hu0)
    nlinarith only [H']
  · have H : |(r * h 2 2) / q 1 - (r * q 2 * h 1 2) / q 1 ^ 2| ≤ 2 :=
      (core_clock_quotient_bound hd hscaledAP haDP).trans (by norm_num)
    have hid : (coreWeightedJacobian k z y) 1 2 = (k / r * u) *
        ((r * h 2 2) / q 1 - (r * q 2 * h 1 2) / q 1 ^ 2) := by
      change k * (u * h 2 2 / q 1 - u * q 2 * h 1 2 / q 1 ^ 2) = _
      field_simp
    rw [hid, abs_mul, abs_of_nonneg (mul_nonneg (div_nonneg hk0.le hr0.le) hu0)]
    have H' := mul_le_mul_of_nonneg_left H (mul_nonneg (div_nonneg hk0.le hr0.le) hu0)
    have H'' := mul_le_mul_of_nonneg_right hkr hu0
    nlinarith only [H', H'', hu0]
