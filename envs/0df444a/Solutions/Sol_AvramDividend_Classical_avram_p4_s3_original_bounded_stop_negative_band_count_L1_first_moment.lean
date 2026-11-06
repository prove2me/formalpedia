-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:07:09.581022+00:00
-- url     : https://prove2.me/submissions/ba4c5ae9-c8c1-4c2e-beba-acf6a419b8f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical stopped finite-band count has a first, rather than merely
    second, moment bounded by its deterministic original-process intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ)) P ∧
      (∫ ω, (K ω : ℝ) ∂P) ≤ r := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
  let KT : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (K ω : ℝ)) P ∧
    (∫ ω, (K ω : ℝ) ∂P) ≤ r
  have hKle (ω : Ω) : K ω ≤ KT ω := by
    apply Set.ncard_le_ncard
    · intro u hu
      exact ⟨hu.1, (hu.2.1).trans (hτ ω), hu.2.2⟩
    · exact avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hKTcast (ω : Ω) : (N ω).toReal = (KT ω : ℝ) := by
    have hN : N ω = (KT ω : ℝ≥0∞) :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
    rw [hN, ENNReal.toReal_natCast]
  have hfun : (fun ω => (N ω).toReal) =
      (fun ω => (KT ω : ℝ)) := funext hKTcast
  have hFixedI := avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  change Integrable (fun ω => (N ω).toReal) P at hFixedI
  rw [hfun] at hFixedI
  have hKmeas' : Measurable K := hKmeas
  have hKreal : Measurable (fun ω => (K ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKmeas'
  have hKI : Integrable (fun ω => (K ω : ℝ)) P := by
    apply Integrable.mono hFixedI hKreal.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hKle ω
  refine ⟨hKI, ?_⟩
  have hMean := avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n
  change (∫ ω, (N ω).toReal ∂P) = r at hMean
  rw [hfun] at hMean
  calc
    (∫ ω, (K ω : ℝ) ∂P) ≤ (∫ ω, (KT ω : ℝ) ∂P) := by
      apply integral_mono_ae hKI hFixedI
      filter_upwards [] with ω
      exact_mod_cast hKle ω
    _ = r := hMean
