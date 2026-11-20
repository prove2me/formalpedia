-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_dirac_size2_mixed_generator_mesh_uniform_strict_discounted_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:09:44.478388+00:00
-- url     : https://prove2.me/submissions/21076c20-6436-477a-b272-6431b4ef8e5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_public_positive_quadratic_ruinclipped_second_derivative
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Levy_Dirac_negative2_generator_mark_integral_exact
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 1) (hc : X.c = 0)
    (hν : X.ν = Measure.dirac (-2 : ℝ))
    (m : ℕ) (y weight : ℕ → ℝ)
    (hwNonneg : ∀ i ∈ Finset.range m, 0 ≤ weight i)
    (hyInterior : ∀ i ∈ Finset.range m,
      0 < y i ∧ y i ≤ (1 / 5 : ℝ)) :
    let w : ℝ → ℝ := fun z =>
      if z < 0 then 0 else 1 + z + z ^ 2
    (∑ i ∈ Finset.range m,
        weight i * (X.generator w (y i) - (1 / 10 : ℝ) * w (y i))) ≤
      (-1 / 10 : ℝ) * ∑ i ∈ Finset.range m, weight i := by
  dsimp
  let w : ℝ → ℝ := fun z =>
    if z < 0 then 0 else 1 + z + z ^ 2
  have hGenEach (i : ℕ) (hi : i ∈ Finset.range m) :
      X.generator w (y i) - (1 / 10 : ℝ) * w (y i) ≤
        (-1 / 10 : ℝ) := by
    obtain ⟨hyi, hcap⟩ := hyInterior i hi
    have hy0 : 0 ≤ y i := le_of_lt hyi
    have hSecond :
        iteratedDeriv 2 w (y i) = 2 :=
      avram_jump6_A_public_positive_quadratic_ruinclipped_second_derivative
        (y i) hyi
    have hMark :
        (∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) =
            -(1 + y i + (y i) ^ 2) := by
      exact avram_jump6_A_original_Levy_Dirac_negative2_generator_mark_integral_exact
        X hν (y i) hy0 (by linarith)
    have hw : w (y i) = 1 + y i + (y i) ^ 2 := by
      simp only [w, if_neg (not_lt.mpr hy0)]
    have hExact : X.generator w (y i) = 1 - w (y i) := by
      unfold SpectrallyNegativeLevy.generator
      rw [hσ, hc, hSecond, hMark, hw]
      ring
    rw [hExact, hw]
    nlinarith [sq_nonneg (y i)]
  calc
    (∑ i ∈ Finset.range m, weight i *
      (X.generator w (y i) - (1 / 10 : ℝ) * w (y i))) ≤
        (∑ i ∈ Finset.range m, weight i * (-1 / 10 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hGenEach i hi) (hwNonneg i hi)
    _ = (-1 / 10 : ℝ) * ∑ i ∈ Finset.range m, weight i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
