-- Prove2me | solution 1 for AvramDividend.Classical.avram_b70_original_bounded_physical_duration_square_energy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:41:36.292173+00:00
-- url     : https://prove2.me/submissions/96aaadee-4fc3-46e8-ae1e-e909835b83a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine bounded original source clock durations have integrable finite square mesh energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P)
    (hBound : ∀ ω i, i ∈ S → t i ω ≤ T) :
    Integrable (fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  apply Integrable.of_bound hMeas ((S.card : ℝ) * (T : ℝ)^2)
  filter_upwards [] with ω
  have hEach (i : ℕ) (hi : i ∈ S) :
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2 ≤ (T : ℝ)^2 := by
    have htsub : t i ω - s i ω ≤ T :=
      (tsub_le_self).trans (hBound ω i hi)
    have hre : ((t i ω - s i ω : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast htsub
    have hpos : 0 ≤ ((t i ω - s i ω : ℝ≥0) : ℝ) :=
      NNReal.coe_nonneg _
    have hT : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
    nlinarith
  have hSum : (∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) ≤
      ∑ i ∈ S, (T : ℝ)^2 :=
    Finset.sum_le_sum (fun i hi => hEach i hi)
  have hNonneg : 0 ≤ (∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  simp only [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  simpa only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul] using hSum
