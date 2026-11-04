-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_discounted_terminal_integrable_of_random_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:01:40.046741+00:00
-- url     : https://prove2.me/submissions/85f47cdc-ae5b-4b1f-962e-437267002ae9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A genuine integrable random envelope gives L¹ for the original discounted terminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (w : ℝ → ℝ) (W : Ω → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P)
    (B : Ω → ℝ) (hB : Integrable B P)
    (hBound : ∀ᵐ ω ∂P, |w (W ω)| ≤ B ω) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by
  apply Integrable.mono hB hMeas
  filter_upwards [hBound] with ω hw
  have hτ : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
  have hfactor : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hq hτ]
  calc
    ‖Real.exp (-(q * (τ ω : ℝ))) * w (W ω)‖ =
        Real.exp (-(q * (τ ω : ℝ))) * |w (W ω)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ |w (W ω)| := by
      simpa using
        (mul_le_mul_of_nonneg_right hfactor (abs_nonneg (w (W ω))))
    _ ≤ B ω := hw
    _ ≤ ‖B ω‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _