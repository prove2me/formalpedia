-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_quadratic_normalised_bounds_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:35:53.791577+00:00
-- url     : https://prove2.me/submissions/aeffe022-f729-442d-a8cb-4cb94971619f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_upper_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) ∂X.ν) / (((n : ℝ) + 1) ^ 2) -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) /
        (((n : ℝ) + 1) ^ 2) ≤
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2)) ∧
    (X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2) ≤
      X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) ∂X.ν) / (((n : ℝ) + 1) ^ 2)) := by
  let K : ℝ :=
    ∫ y in Ioo (-1 : ℝ) 0,
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) ∂X.ν
  let L : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hsq : 0 < (((n : ℝ) + 1) ^ 2) := sq_pos_of_pos hd
  have hLarge := levy_large_negative_jump_unit_integrable X
  have hlow :
      (X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
          K / (((n : ℝ) + 1) ^ 2)) -
          L / (((n : ℝ) + 1) ^ 2) ≤
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2) := by
    have hbound := psi_lower_bound_by_compensated_small_jumps
      X ((n : ℝ) + 1) hd.le hLarge
    calc
      (X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
          K / (((n : ℝ) + 1) ^ 2)) -
          L / (((n : ℝ) + 1) ^ 2) =
        (X.c * ((n : ℝ) + 1) +
          X.σ ^ 2 * (((n : ℝ) + 1) ^ 2) / 2 +
          K - L) / (((n : ℝ) + 1) ^ 2) := by
        field_simp [ne_of_gt hd] <;> ring
      _ ≤ X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2) := by
        apply (div_le_div_iff_of_pos_right hsq).2
        simpa only [K, L] using hbound
  have hup :
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2) ≤
      X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
        K / (((n : ℝ) + 1) ^ 2) := by
    have hbound := psi_upper_bound_by_compensated_small_jumps
      X ((n : ℝ) + 1) hd.le
    calc
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2) ≤
        (X.c * ((n : ℝ) + 1) +
          X.σ ^ 2 * (((n : ℝ) + 1) ^ 2) / 2 +
          K) / (((n : ℝ) + 1) ^ 2) := by
        apply (div_le_div_iff_of_pos_right hsq).2
        simpa only [K] using hbound
      _ = X.c / ((n : ℝ) + 1) + X.σ ^ 2 / 2 +
          K / (((n : ℝ) + 1) ^ 2) := by
        field_simp [ne_of_gt hd] <;> ring
  exact ⟨hlow, hup⟩
