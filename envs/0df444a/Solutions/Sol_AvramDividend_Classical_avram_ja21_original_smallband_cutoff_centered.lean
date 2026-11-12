-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_smallband_cutoff_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:57:51.824933+00:00
-- url     : https://prove2.me/submissions/c3807fd8-5077-439d-9a88-b17fddaefff9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise29_original_bounded_compensated_band_martingale
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n t
  obtain ⟨hInt, hMart⟩ :=
    avram_anoise29_original_bounded_compensated_band_martingale X hFinite n
  have hzero : (∫ ω, avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω ∂P) = 0 := by
    calc
      (∫ ω, avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω ∂P) =
          (∫ ω, condExp (𝓕.rightCont 0) P
            (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ω ∂P) := by
              symm
              exact integral_condExp (𝓕.rightCont.le 0)
      _ = (∫ ω, avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω ∂P) := by
        exact integral_congr_ae (hMart 0 t (zero_le : (0 : ℝ≥0) ≤ t))
      _ = 0 := by
        simp only [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time,
          integral_zero]
  simpa only [integral_neg, hzero, neg_zero]
