-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a559_BV_finite_activity_true_cash_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:45:42.180496+00:00
-- url     : https://prove2.me/submissions/ea455e2c-64ac-47e9-a710-0f9e79529489

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a561_BV_finite_activity_true_cash_eventual_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
    (hTop : C = ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    (∀ n, Integrable (F n) P) ∧
    (∀ n, (∫ ω, F n ω ∂P) ≤ w x) := by
  classical
  intro δ S F
  obtain ⟨hFI, hLimit⟩ :=
    avram_ga_a561_BV_finite_activity_true_cash_eventual_expected_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTop hActivity
  have hMono :=
    avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
      X x C D hD w q T hT
  refine ⟨hFI, ?_⟩
  intro n
  by_contra hFail
  have hgt : w x < ∫ ω, F n ω ∂P := lt_of_not_ge hFail
  let ε : ℝ := ((∫ ω, F n ω ∂P) - w x) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨m, hnm, hmBound⟩ :=
    ((Filter.eventually_ge_atTop n).and (hLimit ε hε)).exists
  have hAe : ∀ᵐ ω ∂P, F n ω ≤ F m ω := by
    filter_upwards [hMono] with ω hω
    exact hω n m hnm
  have hMean : (∫ ω, F n ω ∂P) ≤ (∫ ω, F m ω ∂P) :=
    integral_mono_ae (hFI n) (hFI m) hAe
  dsimp [ε] at hmBound
  linarith
