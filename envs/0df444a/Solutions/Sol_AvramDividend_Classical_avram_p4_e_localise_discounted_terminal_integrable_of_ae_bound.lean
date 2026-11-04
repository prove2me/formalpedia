-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:53:25.908192+00:00
-- url     : https://prove2.me/submissions/d5e799cf-17e2-4290-9de4-8d6804a3b101

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exponential discount preserves an a.e. bound at the actual nonnegative clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (w : ℝ → ℝ) (W : Ω → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P)
    (B : ℝ)
    (hBound : ∀ᵐ ω ∂P, |w (W ω)| ≤ B) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  apply Integrable.of_bound hMeas B
  filter_upwards [hBound] with ω hw
  have hτ : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
  have hfactor : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hq hτ]
  calc
    ‖Real.exp (-(q * (τ ω : ℝ))) * w (W ω)‖ =
        Real.exp (-(q * (τ ω : ℝ))) * |w (W ω)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * |w (W ω)| := mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
    _ ≤ B := by simpa using hw
