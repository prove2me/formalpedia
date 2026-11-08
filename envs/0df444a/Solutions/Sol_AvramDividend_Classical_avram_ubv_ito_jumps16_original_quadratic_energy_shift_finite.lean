-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps16_original_quadratic_energy_shift_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:00:10.530367+00:00
-- url     : https://prove2.me/submissions/e27104ee-88d2-4773-889a-463d63b9efab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original Lévy-energy assumption controls every finite multiple
of the quadratic mark envelope needed to shift a signed Taylor integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℝ) (hM : 0 ≤ M) :
    (∫⁻ z : ℝ, ENNReal.ofReal
      (2 * (M * min (1 : ℝ) (z ^ 2))) ∂X.ν) ≠ ⊤ := by
  have h2M : 0 ≤ 2 * M := by positivity
  have hm : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2))) := by
    fun_prop
  have hpoint (z : ℝ) :
      ENNReal.ofReal (2 * (M * min (1 : ℝ) (z ^ 2))) =
        ENNReal.ofReal (2 * M) *
          ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) := by
    rw [show 2 * (M * min (1 : ℝ) (z ^ 2)) =
      (2 * M) * min (1 : ℝ) (z ^ 2) by ring]
    exact ENNReal.ofReal_mul h2M
  simp_rw [hpoint]
  rw [MeasureTheory.lintegral_const_mul _ hm]
  exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top X.ν_integrable)
