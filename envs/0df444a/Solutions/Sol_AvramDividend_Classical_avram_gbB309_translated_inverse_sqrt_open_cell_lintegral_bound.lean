-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB309_translated_inverse_sqrt_open_cell_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:04:30.979007+00:00
-- url     : https://prove2.me/submissions/78bc7ff2-c2a4-46a2-a095-d52da9c30b4d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral
import Theorems.Thm_AvramDividend_Classical_avram_gbB303_nonnegative_real_cell_integral_to_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A translated inverse-square-root physical-cell lintegral inherits the real Gaussian identity. -/
theorem solution
    (s δ : ℝ) (hδ : 0 ≤ δ)
    (hf : IntegrableOn
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
      (Set.Ioc s (s + δ)) volume) :
    (∫⁻ t in Set.Ioo s (s + δ),
      ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume) ≤
      ENNReal.ofReal (2 * Real.sqrt δ) := by
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc s (s + δ))]
        (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg (sub_nonneg.mpr ht.1.le) _
  have hreal : (∫ t in s..(s + δ), (t - s) ^ (-(1 / 2 : ℝ))) ≤
      2 * Real.sqrt δ :=
    (avram_gbB280_translated_gaussian_inverse_sqrt_cell_integral s δ).le
  have hIoc :=
    avram_gbB303_nonnegative_real_cell_integral_to_lintegral
      s δ (2 * Real.sqrt δ) hδ
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) hf hnonneg hreal
  exact (lintegral_mono_set Set.Ioo_subset_Ioc_self).trans hIoc
