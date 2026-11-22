-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_ubv_HJB_exact_stopped_cash_preterminal_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:03:13.979584+00:00
-- url     : https://prove2.me/submissions/df95979a-2e54-48c1-8a14-7ffa9f96df19

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual stopped physical dividend cash exactly matches the closed-interval
Stieltjes correction for every zero or strictly pre-ruin stopped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hPre : τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
       V (x + X.X (τ ω) ω)) ≤ 0 := by
  have hSet :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
        Icc (0 : ℝ) (τ ω : ℝ) :=
    avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
      X x D ω τ hPre
  rw [hSet]
  exact avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
    X hBV q hq w C hC hw_cont hw_smooth hw_hjb
    x D hD ω (τ ω) hPre

