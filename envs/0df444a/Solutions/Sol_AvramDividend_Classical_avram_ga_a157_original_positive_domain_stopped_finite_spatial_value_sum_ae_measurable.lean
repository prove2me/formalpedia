-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a157_original_positive_domain_stopped_finite_spatial_value_sum_ae_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:49:37.326389+00:00
-- url     : https://prove2.me/submissions/bec8759b-c1a0-4b7f-89d1-21df29da6885

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
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
    (hAlt : ∀ i, ∀ᵐ ω ∂P, Y i ω = Z i ω ∨
      (0 < Y i ω ∧ 0 < Z i ω)) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, E i ω * (w (Z i ω) - w (Y i ω))) P := by
  exact avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
    P w hw m Y Z E hY hZ hE (by
      intro i hi
      exact hAlt i)
