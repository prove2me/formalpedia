-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_quadratic_gaussian_limit_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:37:12.246239+00:00
-- url     : https://prove2.me/submissions/06fa71ef-43c6-4fe6-9944-10dc09b6ea19

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_quadratic_remainder_tendsto_zero_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_psi_quadratic_normalised_bounds_ws01f
import Theorems.Thm_AvramDividend_Classical_psi_upper_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds (X.σ ^ 2 / 2)) := by
  let K : ℕ → ℝ := fun n =>
    ∫ y in Ioo (-1 : ℝ) 0,
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) ∂X.ν
  let L : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  have hd (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hK : Tendsto
      (fun n : ℕ => K n / (((n : ℝ) + 1) ^ 2))
      atTop (nhds 0) := by
    simpa only [K, integral_div] using
      levy_compensated_quadratic_remainder_tendsto_zero_ws01f X
  have hOne : Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hC : Tendsto
      (fun n : ℕ => X.c / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      hOne.const_mul X.c
  have hInvSq : Tendsto
      (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds 0) := by
    have hp := hOne.mul hOne
    convert hp using 1
    · ext n
      have hdn := ne_of_gt (hd n)
      field_simp
    · simp
  have hL : Tendsto
      (fun n : ℕ => L / (((n : ℝ) + 1) ^ 2))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      hInvSq.const_mul L
  have hA : Tendsto
      (fun n : ℕ =>
        X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
          K n / (((n : ℝ) + 1) ^ 2))
      atTop (nhds (X.σ ^ 2 / 2)) := by
    simpa only [zero_add, add_zero] using
      (hC.add (tendsto_const_nhds (x := X.σ ^ 2 / 2))).add hK
  have hAm : Tendsto
      (fun n : ℕ =>
        (X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
          K n / (((n : ℝ) + 1) ^ 2)) -
          L / (((n : ℝ) + 1) ^ 2))
      atTop (nhds (X.σ ^ 2 / 2)) := by
    simpa only [sub_zero] using hA.sub hL
  have hbounds (n : ℕ) :=
    levy_psi_quadratic_normalised_bounds_ws01f X n
  exact Filter.Tendsto.squeeze hAm hA
    (fun n => (hbounds n).1) (fun n => (hbounds n).2)
