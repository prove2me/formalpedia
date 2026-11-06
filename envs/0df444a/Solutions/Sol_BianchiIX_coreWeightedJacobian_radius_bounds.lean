-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_radius_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:08:17.723351+00:00
-- url     : https://prove2.me/submissions/f09c44aa-d103-45c3-8778-e067dca8135f

import Definitions.Def_BianchiIX_Algebra_CoreAngle
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_wall_difference_bounds {m u w : ℝ} (hu : 0 ≤ u ∧ u ≤ m)
    (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| ≤ m ∧ |u - 2 * w| ≤ 2 * m ∧ |3 * w - u| ≤ 3 * m ∧ |2 * u - w| ≤ 2 * m := by
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end

theorem solution {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let m := (1 / 10000) / k
    let v := y 0 / Real.cosh z
    let b := coreWeightedJacobian k z y
    |b 0 0| ≤ 8 * m ∧ |b 0 1 + v / k| ≤ 8 * m / k ∧ |b 0 2| ≤ 8 * m / v := by
  let r := y 0
  let v := r / Real.cosh z
  let m := (1 / 10000) / k
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  obtain ⟨hr5, hm0, hm, _, _, _, _, hsmall⟩ := coreBootstrap_coefficient_scales hk hr
  obtain ⟨_, _, hg, hd, _, _, hdR, hdU, hdP, _, _, hgR, hgU, hgP⟩ :=
    coreAuxiliary_coefficient_bounds hk hr hv hu hw
  change |q 3| ≤ 2 * r * m at hg
  change 999 / 1000 ≤ q 1 at hd
  change |h 1 0| ≤ m / r ^ 2 at hdR
  change |h 1 1| ≤ 2 * m / r ^ 2 at hdU
  change |h 1 2| ≤ 2 * m / (v * r ^ 2) at hdP
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hv0 : 0 < v := by dsimp [v, r]; linarith
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < q 1 := by linarith
  have hprodR : |q 3 * h 1 0| ≤ m / 10 := by
    calc
      _ = |q 3| * |h 1 0| := abs_mul _ _
      _ ≤ (2 * r * m) * (m / r ^ 2) := mul_le_mul hg hdR (abs_nonneg _) (by positivity)
      _ = 2 * m ^ 2 / r := by field_simp
      _ ≤ 4 * m ^ 2 / r := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg m]) hr0.le
      _ ≤ m / 10 := hsmall
  have hprodU : |q 3 * h 1 1| ≤ m / 10 := by
    calc
      _ = |q 3| * |h 1 1| := abs_mul _ _
      _ ≤ (2 * r * m) * (2 * m / r ^ 2) := mul_le_mul hg hdU (abs_nonneg _) (by positivity)
      _ = 4 * m ^ 2 / r := by field_simp; ring
      _ ≤ m / 10 := hsmall
  have hprodP : |v * q 3 * h 1 2| ≤ m / 10 := by
    calc
      _ = v * |q 3| * |h 1 2| := by rw [abs_mul, abs_mul, abs_of_pos hv0]
      _ ≤ v * (2 * r * m) * (2 * m / (v * r ^ 2)) := by gcongr
      _ = 4 * m ^ 2 / r := by field_simp; ring
      _ ≤ m / 10 := hsmall
  have hvclock : |v * (1 - q 1)| ≤ m := by
    let w := y 2 / v
    have hδ := (core_wall_difference_bounds hu hw).1
    have hδ2 : (y 1 - w) ^ 2 ≤ m ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hm0).mpr hδ
    have hvle : v ≤ r := div_le_self hr0.le (Real.one_le_cosh z)
    have hid : 1 - q 1 = (y 1 - w) ^ 2 / r ^ 2 := by dsimp [q, coreAuxiliary, coreClockFactor, w, v, r]; ring
    rw [hid, abs_of_nonneg (mul_nonneg hv0.le (div_nonneg (sq_nonneg _) (sq_nonneg _)))]
    calc
      _ ≤ r * (m ^ 2 / r ^ 2) := mul_le_mul hvle
        (div_le_div_of_nonneg_right hδ2 (sq_nonneg _)) (by positivity) hr0.le
      _ = m ^ 2 / r := by field_simp
      _ ≤ m := (div_le_iff₀ hr0).mpr (by nlinarith [mul_nonneg hm0 (show 0 ≤ r - m by dsimp [r]; linarith)])
  have hx : |h 3 1 + v - v * (1 - q 1)| ≤ 4 * m := by
    have H := (abs_sub (h 3 1 + v) (v * (1 - q 1))).trans (add_le_add hgU hvclock)
    linarith
  constructor
  · change |h 3 0 / q 1 - q 3 * h 1 0 / q 1 ^ 2| ≤ 8 * m
    have H := core_clock_quotient_bound hd hgR hprodR
    linarith
  constructor
  · have hid : (coreWeightedJacobian k z y) 0 1 + v / k =
        ((h 3 1 + v - v * (1 - q 1)) / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k := by
      change (h 3 1 / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k + v / k = _
      field_simp
      ring
    change |(coreWeightedJacobian k z y) 0 1 + v / k| ≤ 8 * m / k
    rw [hid, abs_div, abs_of_pos hk0]
    apply div_le_div_of_nonneg_right _ hk0.le
    have H := core_clock_quotient_bound hd hx hprodU
    linarith
  · have hvh : |v * h 3 2| ≤ 2 * m := by
      rw [abs_mul, abs_of_pos hv0]
      have H := mul_le_mul_of_nonneg_left hgP hv0.le
      change v * |h 3 2| ≤ v * (2 * m / v) at H
      calc
        _ ≤ v * (2 * m / v) := H
        _ = 2 * m := by field_simp
    have hid : (coreWeightedJacobian k z y) 0 2 =
        ((v * h 3 2) / q 1 - (v * q 3 * h 1 2) / q 1 ^ 2) / v := by
      change h 3 2 / q 1 - q 3 * h 1 2 / q 1 ^ 2 = _
      field_simp
    change |(coreWeightedJacobian k z y) 0 2| ≤ 8 * m / v
    rw [hid, abs_div, abs_of_pos hv0]
    apply div_le_div_of_nonneg_right _ hv0.le
    have H := core_clock_quotient_bound hd hvh hprodP
    linarith
