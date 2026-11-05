-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_residual_L2_cauchy_from_physical_strip_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:46:45.432621+00:00
-- url     : https://prove2.me/submissions/61124bf1-b68e-4269-9349-0f8001670436

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_L2_cauchy_of_source_smalljump_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- A physical original-source compensated-jump isometry yields residual L2 Cauchy estimates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (hIsometry :
      ∀ n m : ℕ,
        Integrable (fun ω : Ω =>
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
        (∫ ω : Ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) ≤
          (T : ℝ) *
            (∫ z in Ioc
              (-(1 / (((min n m : ℕ) : ℝ) + 1)))
              (-(1 / (((max n m : ℕ) : ℝ) + 1))),
              z ^ 2 ∂X.ν)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      Integrable (fun ω : Ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
      (∫ ω : Ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by
  apply avram_p4_h_gaussian_original_residual_L2_cauchy_of_source_smalljump_tail X T
  intro ε hε
  have hT : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hDen : (0 : ℝ) < (T : ℝ) + 1 := by linarith
  have hδ : 0 < ε / ((T : ℝ) + 1) := div_pos hε hDen
  obtain ⟨N, hTail⟩ :=
    avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
      X (ε / ((T : ℝ) + 1)) hδ
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hmin : N ≤ min n m := le_min hn hm
  have hBound :=
    (hTail (min n m) hmin (max n m)).2
  have hEq : ((T : ℝ) + 1) * (ε / ((T : ℝ) + 1)) = ε := by
    field_simp
  obtain ⟨hI, hSquare⟩ := hIsometry n m
  constructor
  · exact hI
  · calc
      _ ≤ (T : ℝ) *
          (∫ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            z ^ 2 ∂X.ν) := hSquare
      _ ≤ (T : ℝ) * (ε / ((T : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hBound) hT
      _ < ε := by nlinarith [hEq]
