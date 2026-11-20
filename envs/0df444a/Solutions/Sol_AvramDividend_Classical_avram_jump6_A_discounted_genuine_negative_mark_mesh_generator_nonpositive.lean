-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_discounted_genuine_negative_mark_mesh_generator_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:15:28.833411+00:00
-- url     : https://prove2.me/submissions/8e37c7cd-4ba0-4d8d-8929-b70b86ffabe6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_marks_genuine_generator_weighted_grid_nonpositive

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
    (q : ℝ) (m : ℕ) (t : ℕ → ℝ≥0) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i) :
    (∑ i ∈ Finset.range m, Real.exp (-(q * (t i : ℝ))) * weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) ≤ 0 := by
  have hWeight : ∀ i ∈ Finset.range m,
      0 ≤ Real.exp (-(q * (t i : ℝ))) * weight i := by
    intro i hi
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hw i hi)
  simpa only [mul_assoc] using
    (avram_jump6_A_large_negative_marks_genuine_generator_weighted_grid_nonpositive
      X hFinite hSupport m y
      (fun i => Real.exp (-(q * (t i : ℝ))) * weight i)
      hy hWeight)
