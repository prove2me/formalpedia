-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_expectation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:52:24.785578+00:00
-- url     : https://prove2.me/submissions/8e1e8c5f-b684-4495-ab38-3bca1e4af13f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integral_square_sum_uncorrelated
import Theorems.Thm_AvramDividend_Classical_avram_ja20_original_cutoff_gaussian_uncorrelated_components
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSq : (∀ (n : ℕ) (t : ℝ≥0), Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P)) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  obtain ⟨G, J, hR, hG2, hJ2, hGJ, hCross, hGmom, hJmom⟩ :=
    avram_ja20_original_cutoff_gaussian_uncorrelated_components X hX hFinite n t
  calc
    (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
      (∫ ω, (G ω + J ω) ^ 2 ∂P) := by
        apply integral_congr_ae
        filter_upwards [hR] with ω hω
        rw [hω]
    _ = (t : ℝ) * X.σ ^ 2 +
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) :=
      avram_ja20_integral_square_sum_uncorrelated P G J _ _
        hG2 hJ2 hGJ hCross hGmom hJmom
