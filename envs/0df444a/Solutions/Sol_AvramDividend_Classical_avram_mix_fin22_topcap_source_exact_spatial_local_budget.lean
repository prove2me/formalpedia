-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin22_topcap_source_exact_spatial_local_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:35:29.230126+00:00
-- url     : https://prove2.me/submissions/e3f55fc3-1892-433d-b3ac-1659fefbb9d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_spatial_clocks_with_cofinality
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_true_clipped_upper_value_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_topcap_compact_reward_L1_of_full_F
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin23_topcap_original_compact_stopped_event_ito_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
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
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) *
      w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤) :
    ∃ (S : ℕ → Ω → ℝ≥0∞) (σk : ℕ → Ω → ℝ≥0) (Fk : ℕ → Ω → ℝ),
      (∀ ω, Monotone (fun k => S k ω)) ∧ (∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤) ∧
      (∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal) ∧
      Measurable σ ∧ (∀ k, Measurable (σk k)) ∧
      (∀ k ω, σk k ω ≤ σ ω) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σk k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, Fk k ω = Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨ (σk k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω else riskProcess X x D (σk k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ k, Measurable (Fk k)) ∧ (∀ k, Integrable (Fk k) P) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A → ∀ k,
        (∫ ω in A ∩ {η : Ω | σk k η ≠ 0}, Fk k ω ∂P) ≤
          w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal) := by
  obtain ⟨S, κ, hSdef, hSmono, hSsup, hκdef, hκstop, hκle, _⟩ :=
    avram_mix_fin20_original_true_spatial_clocks_with_cofinality
      X (n : ℝ≥0) σ hσstop hσbound
  let H : ℕ → Ω → ℝ := fun k ω => Real.exp (-(q * (κ k ω : ℝ))) *
    w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω else riskProcess X x D (κ k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hHsource : ∀ k ω, H k ω = Real.exp (-(q * (κ k ω : ℝ))) *
      w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by intros; rfl
  have hκbound : ∀ k ω, X.X (κ k ω) ω ≤ (k : ℝ) + 1 := by
    intro k ω
    simpa [hκdef k ω, hSdef k ω] using
      (avram_mix_fin22_original_true_clipped_upper_value_bound X ((k : ℝ) + 1) (by positivity) ω (σ ω))
  have hHint : ∀ k, Integrable (H k) P := by
    intro k
    exact (avram_mix_fin22_topcap_compact_reward_L1_of_full_F
      X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD σ hσstop F hFsource hFI κ hκstop hκle hκbound H hHsource k).1
  obtain ⟨hHmeas, hBudget⟩ :=
    avram_mix_fin23_topcap_original_compact_stopped_event_ito_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn σ hσstop
      hσbound hσclip F hFsource hFI hFiniteActivity hCtop
      κ hκstop hκle hκbound H hHsource
  have hσmeas : Measurable σ := avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration σ hσstop
  have hκmeas : ∀ k, Measurable (κ k) := fun k => avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration (κ k) (hκstop k)
  exact ⟨S, κ, H, hSmono, Filter.Eventually.of_forall hSsup, hκdef,
    hσmeas, hκmeas, hκle, hκstop, hHsource, hHmeas, hHint, hBudget⟩
