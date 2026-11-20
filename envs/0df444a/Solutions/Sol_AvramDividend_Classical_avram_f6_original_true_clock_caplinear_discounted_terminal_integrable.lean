-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_clock_caplinear_discounted_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:11:00.071761+00:00
-- url     : https://prove2.me/submissions/b74a8f24-33ba-41e3-ab04-b7710c755718

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_caplinear_cash_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (Cash : ℕ → Ω → ℝ)
    (hCash : ∀ k ω, Cash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hCashI : ∀ k, Integrable (Cash k) P) :
    ∀ k, Integrable (fun ω : Ω =>
      Real.exp (-(q * (σ k ω : ℝ))) *
        (let V : ℝ → ℝ := fun z =>
          if ENNReal.ofReal z ≤ C then w z
          else w C.toReal + (z - C.toReal)
         V (if σ k ω = 0 ∨
           (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
             x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
           else riskProcess X x D (σ k ω) ω))) P := by
  intro k
  have hExact :=
    avram_f6_original_stopped_reward_caplinear_cash_exact
      X x C hC hxc w D hD q σ F hFsource k
  have hDiff : Integrable (fun ω => F k ω - Cash k ω) P :=
    (hFI k).sub (hCashI k)
  apply hDiff.congr
  filter_upwards [] with ω
  have hh := hExact ω
  rw [← hCash k ω] at hh
  exact (sub_eq_iff_eq_add).2 hh
