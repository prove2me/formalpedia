-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB303_nonnegative_real_cell_integral_to_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:29:42.447585+00:00
-- url     : https://prove2.me/submissions/b2e9f7a7-8e01-4a89-8d26-5637c7162600

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A nonnegative integrable physical time density passes from its real integral to product-mass ENNReal form. -/
theorem solution
    (s δ K : ℝ) (hδ : 0 ≤ δ)
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioc s (s + δ)) volume)
    (hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc s (s + δ))] f)
    (hbound : (∫ t in s..(s + δ), f t) ≤ K) :
    (∫⁻ t in Set.Ioc s (s + δ), ENNReal.ofReal (f t) ∂volume) ≤
      ENNReal.ofReal K := by
  have hlim := ofReal_integral_eq_lintegral_ofReal hf hnonneg
  have heq : (∫ t in s..(s + δ), f t ∂volume) =
      ∫ t in Set.Ioc s (s + δ), f t ∂volume := by
    exact intervalIntegral.integral_of_le (by linarith : s ≤ s + δ)
  rw [← hlim]
  exact ENNReal.ofReal_le_ofReal (by simpa only [heq] using hbound)
