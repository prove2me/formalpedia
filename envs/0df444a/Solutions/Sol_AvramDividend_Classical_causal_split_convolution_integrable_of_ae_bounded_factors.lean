-- Prove2me | solution 1 for AvramDividend.Classical.causal_split_convolution_integrable_of_ae_bounded_factors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:34:08.359901+00:00
-- url     : https://prove2.me/submissions/24fd7afe-b42e-4d57-9214-8ac9cbaacd81

import Mathlib.Analysis.Convolution

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Opposite bounded factors give integrability on both sides of the causal cutoff. -/
theorem solution
    (κ F : ℝ → ℝ) (x u C B : ℝ) (h0u : 0 ≤ u) (hux : u ≤ x)
    (hFleftInt : IntegrableOn F (Ioc (0 : ℝ) u) volume)
    (hKleftMeas : AEStronglyMeasurable
      (fun s : ℝ => κ (x - s)) (volume.restrict (Ioc (0 : ℝ) u)))
    (hKleftBound : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) u)),
      ‖κ (x - s)‖ ≤ C)
    (hKrightInt : IntegrableOn (fun s : ℝ => κ (x - s)) (Ioc u x) volume)
    (hFrightMeas : AEStronglyMeasurable F (volume.restrict (Ioc u x)))
    (hFrightBound : ∀ᵐ s ∂(volume.restrict (Ioc u x)), ‖F s‖ ≤ B) :
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 u ∧
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume u x := by
  have hleft : IntegrableOn (fun s : ℝ => κ (x - s) * F s)
      (Ioc (0 : ℝ) u) volume :=
    hFleftInt.bdd_mul hKleftMeas hKleftBound
  have hright : IntegrableOn (fun s : ℝ => κ (x - s) * F s)
      (Ioc u x) volume :=
    hKrightInt.mul_bdd hFrightMeas hFrightBound
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h0u).2 hleft,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hux).2 hright⟩
