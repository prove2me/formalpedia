-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_split_product_integrable_of_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:00:41.684906+00:00
-- url     : https://prove2.me/submissions/9a0a57cc-fa2d-433c-97f0-7dc140b88ae4

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_split_convolution_integrable_of_ae_bounded_factors
import Theorems.Thm_AvramDividend_Classical_causal_antitone_left_cutoff_kernel_norm_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Reciprocal positive-time control gives integrability on both cutoff pieces. -/
theorem solution
    (κ F : ℝ → ℝ) (x u A : ℝ)
    (hu : 0 < u) (hux : u < x) (hA : 0 ≤ A)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hFnonneg : ∀ s : ℝ, 0 < s → 0 ≤ F s)
    (hFpoint : ∀ s : ℝ, 0 < s → F s ≤ A / s)
    (hFleftInt : IntegrableOn F (Ioc (0 : ℝ) u) volume)
    (hKleftMeas : AEStronglyMeasurable
      (fun s : ℝ => κ (x - s)) (volume.restrict (Ioc (0 : ℝ) u)))
    (hKrightInt : IntegrableOn (fun s : ℝ => κ (x - s)) (Ioc u x) volume)
    (hFrightMeas : AEStronglyMeasurable F (volume.restrict (Ioc u x))) :
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 u ∧
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume u x := by
  have hKbound :
      ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) u)), ‖κ (x - s)‖ ≤ κ (x - u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact AvramDividend.Classical.causal_antitone_left_cutoff_kernel_norm_bound
      κ x u s hu hux hanti hKnonneg hs
  have hFbound :
      ∀ᵐ s ∂(volume.restrict (Ioc u x)), ‖F s‖ ≤ A / u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans hu hs.1
    have hFn : 0 ≤ F s := hFnonneg s hspos
    calc
      ‖F s‖ = F s := by simp [Real.norm_eq_abs, abs_of_nonneg hFn]
      _ ≤ A / s := hFpoint s hspos
      _ ≤ A / u := div_le_div_of_nonneg_left hA hu hs.1.le
  exact AvramDividend.Classical.causal_split_convolution_integrable_of_ae_bounded_factors
    κ F x u (κ (x - u)) (A / u) hu.le hux.le hFleftInt
    hKleftMeas hKbound hKrightInt hFrightMeas hFbound
