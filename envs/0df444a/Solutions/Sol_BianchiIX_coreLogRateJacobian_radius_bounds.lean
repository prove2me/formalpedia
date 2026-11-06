-- Prove2me | solution 1 for BianchiIX.coreLogRateJacobian_radius_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:30:46.254253+00:00
-- url     : https://prove2.me/submissions/6865f37c-d43f-474c-b5fd-26461911cc05

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Theorems.Thm_BianchiIX_coreAuxiliary_coefficient_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_coefficient_scales
import Theorems.Thm_BianchiIX_core_log_quotient_bound
import Theorems.Thm_BianchiIX_core_log_weak_products
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
    let r := y 0
    let m := (1 / 10000) / k
    let J := coreLogRateJacobian z y
    |J 0 0| ≤ 2 ∧ |J 0 1| ≤ (7 / 2) * m / r ∧ |J 0 2| ≤ 2 / r ∧
      |J 1 0| ≤ 5 / r ^ 2 ∧ |J 1 1| ≤ 6 ∧ |J 1 2| ≤ (7 / 2) * m / r := by
  intro r m J
  let v := r / Real.cosh z
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  obtain ⟨hr5, hm0, hm, hrm, hmr, _, _, _⟩ := coreBootstrap_coefficient_scales hk hr
  obtain ⟨hC, ha, _, hd, hCR, hCU, hdR, hdU, hdP, haR, haP, _⟩ :=
    coreAuxiliary_coefficient_bounds hk hr hv hu hw
  change 0 ≤ q 0 ∧ q 0 ≤ 1 / 100 at hC
  change |q 2| ≤ r at ha
  change 999 / 1000 ≤ q 1 at hd
  change |h 0 0| ≤ y 1 at hCR
  change |h 0 1| ≤ 2 * r at hCU
  change |h 1 0| ≤ m / r ^ 2 at hdR
  change |h 1 1| ≤ 2 * m / r ^ 2 at hdU
  change |h 1 2| ≤ 2 * m / (v * r ^ 2) at hdP
  change |h 2 0| ≤ 3 / 4 at haR
  change |h 2 2| ≤ 1 / r at haP
  change m / r ≤ 1 / 100 at hmr
  change r * m ≤ 1 / 1000 at hrm
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr5]
  have hv0 : 0 < v := by dsimp [v, r]; linarith only [hv]
  have hd0 : 0 < q 1 := by linarith only [hd]
  have hmr0 : 0 ≤ m / r := div_nonneg hm0 hr0.le
  have hprod (i : Fin 3) {B : ℝ} (hB : |h 1 i| ≤ B) : |q 2 * h 1 i| ≤ r * B := by
    rw [abs_mul]
    exact mul_le_mul ha hB (abs_nonneg _) hr0.le
  have hpR : |q 2 * h 1 0| ≤ m / r := by
    convert! hprod 0 hdR using 1
    field_simp
  have hpU : |q 2 * h 1 1| ≤ 2 * m / r := by
    convert! hprod 1 hdU using 1
    field_simp
  have hpP : |q 2 * h 1 2| ≤ 2 * m / r := by
    calc
      _ ≤ r * (2 * m / (v * r ^ 2)) := hprod 2 hdP
      _ = (2 * m / r) / v := by field_simp
      _ ≤ 2 * m / r := div_le_self (by positivity) hv
  have haU : |h 2 1| ≤ m / r := by
    change |y 1 / r| ≤ m / r
    rw [abs_div, abs_of_nonneg hu.1, abs_of_pos hr0]
    exact div_le_div_of_nonneg_right hu.2 hr0.le
  have hCP : |h 0 2| ≤ m := by
    change |y 1 / v| ≤ m
    rw [abs_of_nonneg (div_nonneg hu.1 hv0.le)]
    exact (div_le_self hu.1 hv).trans hu.2
  have hnumR : |2 * (1 + q 0) / r ^ 2 - 2 * h 0 0 / r| ≤ 3 / r ^ 2 := by
    calc
      _ ≤ |2 * (1 + q 0) / r ^ 2| + |2 * h 0 0 / r| := abs_sub _ _
      _ = 2 * (1 + q 0) / r ^ 2 + 2 * |h 0 0| / r := by
        rw [abs_of_nonneg (by have := hC.1; positivity : 0 ≤ 2 * (1 + q 0) / r ^ 2),
          abs_div, abs_mul, abs_of_pos hr0]
        norm_num
      _ ≤ 2 * (1 + q 0) / r ^ 2 + 2 * m / r := by
        gcongr
        exact hCR.trans hu.2
      _ = (2 * (1 + q 0) + 2 * r * m) / r ^ 2 := by field_simp
      _ ≤ 3 / r ^ 2 := div_le_div_of_nonneg_right (by linarith only [hC.2, hrm]) (sq_nonneg r)
  have hnumU : |-2 * h 0 1 / r| ≤ 4 := by
    rw [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    calc
      2 * |h 0 1| / r ≤ 2 * (2 * r) / r := by gcongr
      _ = 4 := by field_simp; norm_num
  have hnumP : |-2 * h 0 2 / r| ≤ 2 * m / r := by
    rw [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCP (by norm_num)) hr0.le
  have hweak (i : Fin 3) {B : ℝ} (hB : |h 1 i| ≤ B) :
      |-(2 * (1 + q 0) / r) * h 1 i| ≤ (2 * (1 + q 0) / r) * B := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by have := hC.1; positivity : 0 ≤ 2 * (1 + q 0) / r)]
    exact mul_le_mul_of_nonneg_left hB (by have := hC.1; positivity)
  obtain ⟨hwR, hwU, hwP⟩ := core_log_weak_products hr5 ⟨hm0, hm⟩ hv hC
  have hpwR := (hweak 0 hdR).trans hwR
  have hpwU := (hweak 1 hdU).trans hwU
  have hpwP := (hweak 2 hdP).trans hwP
  change |-(2 * (1 + q 0) / r) * h 1 0| ≤ 1 / r ^ 2 at hpwR
  change |-(2 * (1 + q 0) / r) * h 1 2| ≤ m / r at hpwP
  have hsmall : 11 / 10 * (m / r + 2 * m / r) ≤ (7 / 2) * m / r := by
    convert! mul_le_mul_of_nonneg_right (show (33 / 10 : ℝ) ≤ 7 / 2 by norm_num) hmr0 using 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change |h 2 0 / q 1 - q 2 * h 1 0 / q 1 ^ 2| ≤ 2
    have H := core_log_quotient_bound hd haR hpR
    linarith only [H, hmr]
  · change |h 2 1 / q 1 - q 2 * h 1 1 / q 1 ^ 2| ≤ (7 / 2) * m / r
    have H := core_log_quotient_bound hd haU hpU
    exact H.trans hsmall
  · change |h 2 2 / q 1 - q 2 * h 1 2 / q 1 ^ 2| ≤ 2 / r
    have H := core_log_quotient_bound hd haP hpP
    calc
      _ ≤ 11 / 10 * (1 / r + 2 * m / r) := H
      _ = (11 / 10 * (1 + 2 * m)) / r := by ring
      _ ≤ 2 / r := div_le_div_of_nonneg_right (by linarith only [hm]) hr0.le
  · have heq : J 1 0 = (2 * (1 + q 0) / r ^ 2 - 2 * h 0 0 / r) / q 1 -
        (-(2 * (1 + q 0) / r) * h 1 0) / q 1 ^ 2 := by
      change 2 * (1 + q 0) / (r ^ 2 * q 1) - 2 * h 0 0 / (r * q 1) +
        2 * (1 + q 0) * h 1 0 / (r * q 1 ^ 2) = _
      field_simp
      ring
    rw [heq]
    have H := core_log_quotient_bound hd hnumR hpwR
    apply H.trans
    convert! mul_le_mul_of_nonneg_right (show (22 / 5 : ℝ) ≤ 5 by norm_num)
      (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (sq_nonneg r)) using 1 <;> ring
  · have heq : J 1 1 = (-2 * h 0 1 / r) / q 1 - (-(2 * (1 + q 0) / r) * h 1 1) / q 1 ^ 2 := by
      change -2 * h 0 1 / (r * q 1) + 2 * (1 + q 0) * h 1 1 / (r * q 1 ^ 2) = _
      field_simp
      ring
    rw [heq]
    have H := core_log_quotient_bound hd hnumU hpwU
    linarith only [H]
  · have heq : J 1 2 = (-2 * h 0 2 / r) / q 1 - (-(2 * (1 + q 0) / r) * h 1 2) / q 1 ^ 2 := by
      change -2 * h 0 2 / (r * q 1) + 2 * (1 + q 0) * h 1 2 / (r * q 1 ^ 2) = _
      field_simp
      ring
    rw [heq]
    have H := core_log_quotient_bound hd hnumP hpwP
    rw [add_comm (2 * m / r) (m / r)] at H
    exact H.trans hsmall
