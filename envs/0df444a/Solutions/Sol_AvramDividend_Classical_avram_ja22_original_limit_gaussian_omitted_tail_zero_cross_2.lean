-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja22_original_limit_gaussian_omitted_tail_zero_cross
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:12:42.901468+00:00
-- url     : https://prove2.me/submissions/b6af819b-ad5b-48b8-b30b-68ead6c60701
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical Gaussian-limit and omitted negative-mark source covariance vanishes from positive-time independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, R t ω *
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ∂P) =
      0 := by
  intro n t
  by_cases ht : t = 0
  · subst t
    have hZero :=
      avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
        X R hR
    have heq : (fun ω => R 0 ω *
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω - R 0 ω)) =ᵐ[P]
        (fun _ : Ω => (0 : ℝ)) := by
      filter_upwards [hZero] with ω hω
      rw [hω]
      ring
    calc
      (∫ ω, R 0 ω *
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω - R 0 ω) ∂P) =
          (∫ _ω : Ω, (0 : ℝ) ∂P) := integral_congr_ae heq
      _ = 0 := by simp
  · have htpos : (0 : ℝ≥0) < t := by
      exact lt_of_le_of_ne (bot_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
    obtain ⟨hIndep, hIntR, hIntJ, hCentred⟩ :=
      avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
        X hX hFinite R hR n t htpos
    have hProduct :
        (∫ ω, R t ω *
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ∂P) =
        (∫ ω, R t ω ∂P) *
          (∫ ω,
            avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω ∂P) :=
      hIndep.integral_mul_eq_mul_integral hIntR.aestronglyMeasurable hIntJ.aestronglyMeasurable
    rw [hCentred] at hProduct
    simpa using hProduct
