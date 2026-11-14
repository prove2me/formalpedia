-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a57_original_BV_ruinclipped_true_cash_survivor_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:57:18.300899+00:00
-- url     : https://prove2.me/submissions/817c721c-244a-4fbc-8cc5-82b3d69acd39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ (n : ℕ) (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
      (∀ ω, W ω =
        if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) →
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) →
      (∀ ω,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ Cash ω) →
      (∀ ω,
          (S : ℝ≥0∞) < ruinTime X x D ω →
            Term ω = Real.exp (-(q * T)) * w (riskProcess X x D S ω)) →
      ∀ᵐ ω ∂P, F n ω ≤ Term ω + Cash ω := by
  classical
  intro δ S F n τ W Cash Term hW hTerm hPrefix hSurv
  have hSmooth : (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hn
      exact False.elim (hn hBV)
    · intro _
      exact hw_smooth
  have hTermNN : ∀ᵐ ω ∂P, 0 ≤ Term ω :=
    avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
      X q w C hC hw0 hw_cont hw_neg hSmooth
      hw_grad x hx hxc D hD τ W Term hW hTerm
  filter_upwards [hTermNN] with ω hnn
  change
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ≤
      Term ω + Cash ω
  by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hs]
    rw [hSurv ω hs]
    linarith [hPrefix ω]
  · simp only [if_neg hs]
    linarith [hPrefix ω]
