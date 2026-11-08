-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn8_original_F_vanishing_localisation_events_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:04:16.363943+00:00
-- url     : https://prove2.me/submissions/af19eb9f-325a-499c-b72e-d81e8f32e843

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any sequence of negligible measurable localisation events makes the
source-exact stopped payoff negligible in L1 on those same events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (A : ℕ → Set Ω) (hA : ∀ k, MeasurableSet (A k))
    (hPA : Tendsto (fun k => P (A k)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((A k).indicator (F k)) (1 : ℝ≥0∞) P)
      atTop (𝓝 0) := by
  have hUI : UniformIntegrable F (1 : ℝ≥0∞) P :=
    avram_ubv_finite9_turn8_exact_source_F_uniformIntegrable
      X x q hq C hfinite hxc w hw_cont hw_neg D hD
      τ Cash hCash hCashI σ hσle F hFsource hFI
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨0, ?_⟩
    intro k hk
    simp [htop]
  have hεreal : 0 < ε.toReal :=
    ENNReal.toReal_pos (ne_of_gt hε) htop
  obtain ⟨δ, hδ, hsmall⟩ := hUI.unifIntegrable hεreal
  have hδenn : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  rw [ENNReal.tendsto_atTop_zero] at hPA
  obtain ⟨N, hN⟩ := hPA (ENNReal.ofReal δ) hδenn
  refine ⟨N, ?_⟩
  intro k hk
  calc
    eLpNorm ((A k).indicator (F k)) (1 : ℝ≥0∞) P ≤
        ENNReal.ofReal ε.toReal := hsmall k (A k) (hA k) (hN k hk)
    _ = ε := ENNReal.ofReal_toReal htop
