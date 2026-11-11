-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise31_original_smallband_signed_rightcont_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:48:02.643381+00:00
-- url     : https://prove2.me/submissions/357f068d-1345-43a9-a813-569aa46d6c45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_anoise32_original_smallband_signed_increment_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original finite-band martingale follows from original adaptedness and
the source-exact centring of its future signed-mark increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ω =
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n s t hst
  let S (u : ℝ≥0) : Ω → ℝ :=
    fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω
  let R (k : ℕ) (u : ℝ≥0) : Ω → ℝ :=
    fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω
  have hS_eq : S s = (fun ω => R 0 s ω - R n s ω) := by
    funext ω
    have hz : avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 s ω = 0 := by
      simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
    have he := avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
      X n 0 s ω
    dsimp [S, R] at *
    rw [hz] at he
    simp only [zero_sub] at he
    linarith
  have hSmeas : Measurable[𝓕.rightCont s] (S s) := by
    rw [hS_eq]
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X 0 s).sub (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n s)).mono (𝓕.le_rightCont s) le_rfl
  have hSelf : condExp (𝓕.rightCont s) P (S s) = S s :=
    condExp_of_stronglyMeasurable (𝓕.rightCont.le s)
      hSmeas.stronglyMeasurable (hInt n s)
  have hSub := condExp_sub (hInt n t) (hInt n s) (𝓕.rightCont s)
  have hZero := avram_anoise32_original_smallband_signed_increment_condexp_zero
    X hFinite hInt n s t hst
  filter_upwards [hSub, hZero] with ω hSubω hZeroω
  change condExp (𝓕.rightCont s) P (S t) ω = S s ω
  apply sub_eq_zero.mp
  calc
    condExp (𝓕.rightCont s) P (S t) ω - S s ω =
        condExp (𝓕.rightCont s) P (S t) ω -
          condExp (𝓕.rightCont s) P (S s) ω := by rw [hSelf]
    _ = condExp (𝓕.rightCont s) P (fun ω => S t ω - S s ω) ω := hSubω.symm
    _ = 0 := hZeroω
