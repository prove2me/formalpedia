-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_weighted_time_mark_grid_compensation_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:17:09.839978+00:00
-- url     : https://prove2.me/submissions/e1f371bc-d9fb-4274-a05d-8604328059bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original source cellwise weighted P2 rates yield the finite-grid
nonnegative jump-integral compensator identity under physical P. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (timeMeasure : Measure ℝ≥0)
    (N : Ω → Measure (ℝ≥0 × ℝ))
    (hN : ∀ ω, N ω =
      (Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable (H i))
    (hCount : ∀ i ∈ S, Measurable
      (fun ω => N ω (Ioc (s i) (t i) ×ˢ B i)))
    (hRate : ∀ i ∈ S,
      (∫⁻ ω, H i ω * N ω (Ioc (s i) (t i) ×ˢ B i) ∂P) =
      (∫⁻ ω, H i ω *
        (timeMeasure.prod X.ν) (Ioc (s i) (t i) ×ˢ B i) ∂P)) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => H i ω) p ∂N ω) ∂P) =
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => H i ω) p ∂(timeMeasure.prod X.ν)) ∂P) := by
  have hRaw (ω : Ω) :
      (∫⁻ p : ℝ≥0 × ℝ, ∑ i ∈ S,
        (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p ∂N ω) =
      ∑ i ∈ S, H i ω * N ω (Ioc (s i) (t i) ×ˢ B i) := by
    simpa only [← hN ω] using
      (avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
        X S s t B hB H ω)
  have hComp (ω : Ω) :
      (∫⁻ p : ℝ≥0 × ℝ, ∑ i ∈ S,
        (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p
        ∂(timeMeasure.prod X.ν)) =
      ∑ i ∈ S, H i ω *
        (timeMeasure.prod X.ν) (Ioc (s i) (t i) ×ˢ B i) :=
    avram_p4_b_smalljump_original_random_coeff_levy_compensator_time_mark_grid_lintegral
      X timeMeasure S s t B hB H ω
  have hmRaw (i : ι) (hi : i ∈ S) : Measurable
      (fun ω => H i ω * N ω (Ioc (s i) (t i) ×ˢ B i)) :=
    (hH i hi).mul (hCount i hi)
  have hmComp (i : ι) (hi : i ∈ S) : Measurable
      (fun ω => H i ω *
        (timeMeasure.prod X.ν) (Ioc (s i) (t i) ×ˢ B i)) :=
    (hH i hi).mul measurable_const
  calc
    _ = (∫⁻ ω, ∑ i ∈ S,
        H i ω * N ω (Ioc (s i) (t i) ×ˢ B i) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hRaw ω
    _ = ∑ i ∈ S,
        (∫⁻ ω, H i ω * N ω (Ioc (s i) (t i) ×ˢ B i) ∂P) := by
      rw [lintegral_finset_sum S hmRaw]
    _ = ∑ i ∈ S, (∫⁻ ω,
        H i ω * (timeMeasure.prod X.ν) (Ioc (s i) (t i) ×ˢ B i) ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hRate i hi
    _ = (∫⁻ ω, ∑ i ∈ S,
        H i ω * (timeMeasure.prod X.ν) (Ioc (s i) (t i) ×ˢ B i) ∂P) := by
      rw [lintegral_finset_sum S hmComp]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact (hComp ω).symm
