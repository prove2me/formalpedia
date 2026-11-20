-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_true_overshooting_negative_Levy_mesh_compensator_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:42:04.048454+00:00
-- url     : https://prove2.me/submissions/02b7a024-6053-45e2-8a39-7d0dbba17078

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (m : ℕ) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i) :
    (∑ i ∈ Finset.range m, weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) =
      -(X.ν (Iio (0 : ℝ))).toReal *
        (∑ i ∈ Finset.range m, weight i * (1 + y i + y i ^ 2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hyi, hci⟩ := hy i hi
  rw [avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
    X hFinite hSupport (y i) hyi hci]
  ring
