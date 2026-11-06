-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_weak_off_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:09:19.983538+00:00
-- url     : https://prove2.me/submissions/3a700ad5-477f-49f3-8721-1f236fe11b91

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
    |(coreWeightedJacobian k z y) 2 0| ≤ 8 * y 2 / k ^ 2 ∧
    |(coreWeightedJacobian k z y) 2 1| ≤ 8 * y 2 / k := by
  let r := y 0
  let u := y 1
  let p := y 2
  let v := r / Real.cosh z
  let m := (1 / 10000) / k
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  obtain ⟨hr5, hm0, _, hrm, hmr, _, hkr2, _⟩ := coreBootstrap_coefficient_scales hk hr
  obtain ⟨hC, _, _, hd, hCR, hCU, hdR, hdU, _⟩ := coreAuxiliary_coefficient_bounds hk hr hv hu hw
  change 0 ≤ q 0 ∧ q 0 ≤ 1 / 100 at hC
  change 999 / 1000 ≤ q 1 at hd
  change |h 0 0| ≤ u at hCR
  change |h 0 1| ≤ 2 * r at hCU
  change |h 1 0| ≤ m / r ^ 2 at hdR
  change |h 1 1| ≤ 2 * m / r ^ 2 at hdU
  change r * m ≤ 1 / 1000 at hrm
  change m / r ≤ 1 / 100 at hmr
  change k ^ 2 / r ^ 2 ≤ 3 / 2 at hkr2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hv0 : 0 < v := by dsimp [v, r]; linarith
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < q 1 := by linarith
  have hp0 : 0 ≤ p := by
    have H := (le_div_iff₀ hv0).mp hw.1
    simpa only [zero_mul] using H
  have h1C : |1 + q 0| ≤ 11 / 10 := by rw [abs_of_nonneg (by linarith [hC.1])]; linarith [hC.2]
  have hru : r * u ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hu.2 hr0.le).trans hrm
  have hfirst : |2 * (1 + q 0) - 2 * r * h 0 0| ≤ 3 := by
    have H := abs_sub (2 * (1 + q 0)) (2 * r * h 0 0)
    have HC : |2 * (1 + q 0)| ≤ 11 / 5 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith only [h1C]
    have HR : |2 * r * h 0 0| ≤ 2 / 1000 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hr0]
      nlinarith only [hru, mul_le_mul_of_nonneg_left hCR hr0.le]
    linarith only [H, HC, HR]
  have hsecond : |-2 * (1 + q 0) * r * h 1 0| ≤ 1 / 10 := by
    calc
      _ = 2 * |1 + q 0| * r * |h 1 0| := by simp [abs_mul, abs_of_pos hr0]
      _ ≤ 2 * (11 / 10) * r * (m / r ^ 2) := by gcongr
      _ = 11 / 5 * (m / r) := by field_simp; ring
      _ ≤ 1 / 10 := by linarith only [hmr]
  have hthird : |-2 * h 0 1 / r| ≤ 4 := by
    rw [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    apply (div_le_iff₀ hr0).mpr
    linarith only [hCU]
  have hfourth : |-2 * (1 + q 0) * h 1 1 / r| ≤ 1 / 10 := by
    calc
      _ = 2 * |1 + q 0| * |h 1 1| / r := by simp [abs_mul, abs_div, abs_of_pos hr0]
      _ ≤ 2 * (11 / 10) * (2 * m / r ^ 2) / r := by gcongr
      _ = (22 / 5 * (m / r)) / r ^ 2 := by ring
      _ ≤ 22 / 5 * (m / r) := div_le_self (by positivity) (by nlinarith only [hr5, sq_nonneg (r - 5)])
      _ ≤ 1 / 10 := by linarith only [hmr]
  constructor
  · have H : |(2 * (1 + q 0) - 2 * r * h 0 0) / q 1 -
        (-2 * (1 + q 0) * r * h 1 0) / q 1 ^ 2| ≤ 5 :=
      (core_clock_quotient_bound hd hfirst hsecond).trans (by norm_num)
    have hid : (coreWeightedJacobian k z y) 2 0 = p / r ^ 2 *
        ((2 * (1 + q 0) - 2 * r * h 0 0) / q 1 -
        (-2 * (1 + q 0) * r * h 1 0) / q 1 ^ 2) := by
      change 2 * p * (1 + q 0) / (r ^ 2 * q 1) - 2 * p * h 0 0 / (r * q 1) +
        2 * p * (1 + q 0) * h 1 0 / (r * q 1 ^ 2) = _
      field_simp
      ring
    rw [hid, abs_mul, abs_of_nonneg (div_nonneg hp0 (sq_nonneg _))]
    calc
      _ ≤ p / r ^ 2 * 5 := mul_le_mul_of_nonneg_left H (div_nonneg hp0 (sq_nonneg _))
      _ ≤ 8 * p / k ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hk0)).mpr
        have H' := mul_le_mul_of_nonneg_left hkr2 hp0
        have E : p / r ^ 2 * 5 * k ^ 2 = 5 * (p * (k ^ 2 / r ^ 2)) := by ring
        rw [E]
        nlinarith only [H', hp0]
  · have H : |(-2 * h 0 1 / r) / q 1 - (-2 * (1 + q 0) * h 1 1 / r) / q 1 ^ 2| ≤ 8 :=
      (core_clock_quotient_bound hd hthird hfourth).trans (by norm_num)
    have hid : (coreWeightedJacobian k z y) 2 1 = p / k *
        ((-2 * h 0 1 / r) / q 1 - (-2 * (1 + q 0) * h 1 1 / r) / q 1 ^ 2) := by
      change (-2 * p * h 0 1 / (r * q 1) + 2 * p * (1 + q 0) * h 1 1 / (r * q 1 ^ 2)) / k = _
      field_simp
      ring
    rw [hid, abs_mul, abs_of_nonneg (div_nonneg hp0 hk0.le)]
    have H' := mul_le_mul_of_nonneg_left H (div_nonneg hp0 hk0.le)
    convert! H' using 1
    ring
