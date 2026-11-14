-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb54_original_true_horizon_reward_expected_from_asymptotic_same_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:12:43.441423+00:00
-- url     : https://prove2.me/submissions/8a7b86e6-335b-46b0-a1bf-5fd70a467255

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Corrected top-cap expected-value route with the original true-horizon
terminal payoff and strictly truncated source cash, using eventual epsilon
budgets instead of the invalid pathwise same-row premature compensated bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    (∀ n, Integrable (F n) P) →
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in (atTop : Filter ℕ), (∫ ω, F m ω ∂P) ≤ w x + ε) →
    ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
  intro δ S F hInt hAsymptotic
  have hMon :=
    avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
      X x C D hD w q T hT
  apply avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
    P F (w x) hInt
  · intro n m hnm
    filter_upwards [hMon] with ω hω
    exact hω n m hnm
  · exact hAsymptotic
