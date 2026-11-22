-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_physical_reciprocal_expected_quantization_width_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:00:37.477641+00:00
-- url     : https://prove2.me/submissions/86353233-1783-4059-bb36-ffeb4472538b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let A : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let δ : ℕ → ℝ := fun i =>
      1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, n ≤ m →
        (∑ i ∈ Finset.Ico n m, δ i * r i) < ε := by
  classical
  intro A r δ ε hε
  have hT : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hScale : 0 < 2 * ((T : ℝ) + 1) := by positivity
  have hSmall : 0 < ε / (2 * ((T : ℝ) + 1)) := by positivity
  obtain ⟨N, hN⟩ :=
    avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
      X (ε / (2 * ((T : ℝ) + 1))) hSmall
  refine ⟨N, ?_⟩
  intro n hn m hnm
  have hW :
      (∑ i ∈ Finset.Ico n m, δ i * r i) ≤
        2 * ((T : ℝ) *
          (∫ z in Ioc (-(1 / ((n : ℝ) + 1)))
            (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) := by
    simpa only [] using
      (avram_twoagentA_original_allnu_finite_reciprocal_mark_width_expected_energy_le_twoV
        X T n m hnm)
  have hQ := (hN n hn m).2
  have hQnonneg :
      0 ≤ (∫ z in Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν) := by
    apply integral_nonneg
    intro z
    positivity
  have hBound : 2 * ((T : ℝ) *
      (∫ z in Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) < ε := by
    have hMul := mul_lt_mul_of_pos_left hQ hScale
    have hCancel :
        2 * ((T : ℝ) + 1) *
          (ε / (2 * ((T : ℝ) + 1))) = ε := by
      field_simp [ne_of_gt hScale]
    rw [hCancel] at hMul
    nlinarith
  exact lt_of_le_of_lt hW hBound
