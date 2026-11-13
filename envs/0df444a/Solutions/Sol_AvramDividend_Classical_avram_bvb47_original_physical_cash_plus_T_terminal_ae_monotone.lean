-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T20:57:10.2878+00:00
-- url     : https://prove2.me/submissions/75077452-df7b-43be-9071-3403dca6f91c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_strict_discounted_cash_toReal_mono
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ᵐ ω ∂P, ∀ n k : ℕ, n ≤ k → F n ω ≤ F k ω := by
  intro δ S F
  have hFinite :=
    avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
      X x C D hD T (le_of_lt hT) q
  filter_upwards [hFinite] with ω hFiniteω
  intro n k hnk
  have hCash :=
    avram_bvb45_original_strict_discounted_cash_toReal_mono
      T hT q (ruinTime X x D ω) (dividendMeasure D ω)
      hFiniteω n k hnk
  dsimp only [F, δ]
  linarith only [hCash]
