-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop18_original_physical_compact_clock_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T01:35:34.181234+00:00
-- url     : https://prove2.me/submissions/9ce04ef7-1f47-4ec9-853b-b1ca1bd37724

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gtop20_original_lower_exit_cofinal_floor_clocks
import Theorems.Thm_AvramDividend_Classical_avram_gtop20_original_upper_envelope_splice_of_cofinal_floor
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
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (ρ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, ρ j ω ≤ σ ω) ∧
      (∀ ω, Monotone (fun j : ℕ => ρ j ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω))) ∧
      (∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
        riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) := by
  obtain ⟨L, hLstop, hLle, hLmono, hLlim, hLfloor⟩ :=
    avram_gtop20_original_lower_exit_cofinal_floor_clocks
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop σ hσstop hσle
  exact avram_gtop20_original_upper_envelope_splice_of_cofinal_floor
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop σ hσstop hσle
    L hLstop hLle hLmono hLlim hLfloor
