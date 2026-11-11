-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_zero_cutoff_increment_mean_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:13:51.910204+00:00
-- url     : https://prove2.me/submissions/d3ae2bfb-9a2f-41e7-b334-b628e759c207
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_largejump_sum_L1_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_time_mean_triplet
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_largejump_sum_signed_mean_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The source-exact zero-cutoff residual is centred because its original X
and original large-negative-jump sum have matching Levy triplet means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ s t : ℝ≥0, s ≤ t →
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  let J (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
  have hRInt := avram_ja18_zero_cutoff_fixed_time_integrable X hX hFinite
  have hZero (t : ℝ≥0) : (∫ ω, R t ω ∂P) = 0 := by
    have hXi : Integrable (X.X t) P :=
      avram_ja18_standing_X_integrable_fixedtime X hX t
    have hJi : Integrable (J t) P :=
      avram_ja18_original_largejump_sum_L1_of_standing X hX hFinite t
    have hCi : Integrable (fun _ : Ω => (t : ℝ) * X.c) P :=
      integrable_const _
    have hXYi : Integrable (fun ω => X.X t ω - (t : ℝ) * X.c) P :=
      hXi.sub hCi
    have hEq : R t =
        (fun ω => X.X t ω - (t : ℝ) * X.c - J t ω) := by
      funext ω
      simp [R, J, avram_p4_h_gaussian_intrinsic_truncated_residual,
        avram_p4_h_gaussian_intrinsic_small_band_compensated]
    rw [hEq, integral_sub hXYi hJi, integral_sub hXi hCi]
    simp only [integral_const, measure_univ, ENNReal.toReal_one, one_smul]
    rw [avram_ja18g_original_levy_X_time_mean_triplet X hX hFinite t,
      avram_ja18g_original_largejump_sum_signed_mean_triplet X hX hFinite t]
    have hProb : P.real Set.univ = 1 := by
      change (P Set.univ).toReal = 1
      simp
    rw [hProb]
    ring
  intro s t hst
  change (∫ ω, R t ω - R s ω ∂P) = 0
  rw [integral_sub (hRInt t) (hRInt s), hZero t, hZero s]
  ring
