-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:27:55.911489+00:00
-- url     : https://prove2.me/submissions/621d9434-ec60-4c90-80cd-9ed2485930a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (Y Z E : Ω → ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) (hE : Measurable E)
    (hAlt : ∀ᵐ ω ∂P,
      Y ω = Z ω ∨ (0 < Y ω ∧ 0 < Z ω)) :
    AEStronglyMeasurable (fun ω => E ω * (w (Z ω) - w (Y ω))) P := by
  have h := avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
    P w hw 1 (fun _ => Y) (fun _ => Z) (fun _ => E)
    (fun _ => hY) (fun _ => hZ) (fun _ => hE)
    (fun i hi => hAlt)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using h
