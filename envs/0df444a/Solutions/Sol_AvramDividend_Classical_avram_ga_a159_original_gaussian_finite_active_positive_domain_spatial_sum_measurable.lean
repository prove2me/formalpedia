-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:45:58.30443+00:00
-- url     : https://prove2.me/submissions/35cae1ab-608f-43fb-b152-d03c2dcb39f6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a156_original_positive_domain_spatial_value_difference_ae_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (m : ℕ) (Y Z E : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hZ : ∀ i, Measurable (Z i))
    (hE : ∀ i, Measurable (E i))
    (hAlt : ∀ i ∈ Finset.range m, ∀ᵐ ω ∂P,
      Y i ω = Z i ω ∨ (0 < Y i ω ∧ 0 < Z i ω)) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, E i ω * (w (Z i ω) - w (Y i ω))) P := by
  classical
  have hSum : AEStronglyMeasurable
      (∑ i ∈ Finset.range m,
        fun ω : Ω => E i ω * (w (Z i ω) - w (Y i ω))) P := by
    exact Finset.aestronglyMeasurable_sum (Finset.range m) (fun i hi =>
      avram_ga_a156_original_positive_domain_spatial_value_difference_ae_measurable
        P w hw (Y i) (Z i) (E i) (hY i) (hZ i) (hE i)
        (hAlt i hi))
  refine (aestronglyMeasurable_congr ?_).mp hSum
  filter_upwards [] with ω
  simp only [Finset.sum_apply]
