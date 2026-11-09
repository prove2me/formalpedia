-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed11_original_uniform_residual_from_physical_smalljump_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T09:50:05.510202+00:00
-- url     : https://prove2.me/submissions/008292e1-cd02-451c-85bd-0311000ca284

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine same-process small-jump strip isometry at physical times
implies a cutoff shared by every stopped horizon below H. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (H : ℝ≥0)
    (hSmallIso : ∀ (n m : ℕ) (T : ℝ≥0), T ≤ H →
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
         avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
         avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) ≤
        (T : ℝ) *
          (∫ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            z ^ 2 ∂X.ν)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ m : ℕ, N ≤ m →
          ∀ T : ℝ≥0, T ≤ H →
            Integrable (fun ω =>
              (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
               avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
            (∫ ω,
              (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
               avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by
  intro ε hε
  have hden : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have heps : 0 < ε / ((H : ℝ) + 1) := div_pos hε hden
  obtain ⟨N, hN⟩ :=
    avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail X _ heps
  refine ⟨N, ?_⟩
  intro n hn m hm T hT
  obtain ⟨hSmallI, hSmallBound⟩ := hSmallIso n m T hT
  obtain ⟨hTransferI, hTransferEq⟩ :=
    avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer X n m T
  have hMin : N ≤ min n m := le_min hn hm
  obtain ⟨hStripI, hStrip⟩ := hN (min n m) hMin (max n m)
  have hTN : (T : ℝ) ≤ (H : ℝ) := by exact_mod_cast hT
  have hNonneg : 0 ≤
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) :=
    integral_nonneg (fun z => sq_nonneg z)
  refine ⟨hTransferI.mpr hSmallI, ?_⟩
  rw [hTransferEq]
  have hStep : (T : ℝ) *
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) ≤
      ((H : ℝ) + 1) *
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) := by nlinarith
  have hStrict : ((H : ℝ) + 1) *
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) <
      ((H : ℝ) + 1) * (ε / ((H : ℝ) + 1)) :=
    mul_lt_mul_of_pos_left hStrip hden
  have hCancel : ((H : ℝ) + 1) * (ε / ((H : ℝ) + 1)) = ε := by
    field_simp
  linarith
