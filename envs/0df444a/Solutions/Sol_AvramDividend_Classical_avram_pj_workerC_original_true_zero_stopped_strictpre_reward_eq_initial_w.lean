-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:42:38.33663+00:00
-- url     : https://prove2.me/submissions/0830d971-99ff-4429-b65b-d03e3f4bd2ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger125_original_zero_clock_cash_components_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ρ : Ω → ℝ≥0)
    (V : Ω → ℝ)
    (hV : ∀ ω, V ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, ρ ω = 0 → V ω = w x := by
  intro ω hρzero
  have hDzero : D 0 ω = 0 := hD.1.1.1 ω
  have hXzero : X.X 0 ω = 0 := X.X_zero ω
  have hCashZero :=
    (avram_gledger125_original_zero_clock_cash_components_vanish
      D ω (ruinTime X x D ω) q 1).1
  rw [hV ω, hρzero]
  simpa [riskProcess, hDzero, hXzero] using hCashZero
