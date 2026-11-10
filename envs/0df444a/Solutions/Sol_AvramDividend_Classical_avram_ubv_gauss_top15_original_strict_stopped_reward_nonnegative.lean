-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:40:20.48154+00:00
-- url     : https://prove2.me/submissions/67898210-8a92-4c05-a403-67eaba988545

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) :
    ∀ k ω,
      0 ≤ (if σ k ω = 0 then w x else
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) := by
  have hW : ∀ y : ℝ, 0 ≤ w y :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTopCap hw0 hw_cont hw_neg hw_smooth hw_grad
  intro k ω
  by_cases hz : σ k ω = 0
  · simp only [if_pos hz]
    exact hW x
  · simp only [if_neg hz]
    exact add_nonneg
      (mul_nonneg (le_of_lt (Real.exp_pos _))
        (hW (riskProcess X x D (σ k ω) ω)))
      ENNReal.toReal_nonneg
