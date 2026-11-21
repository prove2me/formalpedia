-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_B_original_positive_expected_budget_topcap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:32:21.791569+00:00
-- url     : https://prove2.me/submissions/bb245221-cd0d-4af1-881e-84f4e575de89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_physical_five_signed_ito_components_topcap
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_supported_mean_zero_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
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
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤)
    (hCapCase : C = ⊤) :
    ∀ k, (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨Mc, Ms, Ml, G, R, hMc, hMs, hMl, hzMc, hzMs, hzMl,
    hOffMc, hOffMs, hOffMl, hG, hR, hUpper⟩ :=
    AvramDividend.Classical.avram_mix_inf20_original_physical_five_signed_ito_components_topcap
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI hInfiniteActivity hCapCase k
  let M := fun ω => Mc ω + Ms ω + Ml ω
  have hMI : Integrable M P := (hMc.add hMs).add hMl
  have hMean : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, Mc ω + Ms ω + Ml ω ∂P) = 0
    have h12 : (∫ ω, Mc ω + Ms ω ∂P) =
        (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) := by
      exact integral_add hMc hMs
    have h123 : (∫ ω, (Mc ω + Ms ω) + Ml ω ∂P) =
        (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
      exact integral_add (hMc.add hMs) hMl
    calc
      (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
          (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) := h123
      _ = (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
        rw [h12]
      _ = 0 := by rw [hzMc, hzMs, hzMl]; ring
  have hOff : ∀ᵐ ω ∂P, σ k ω = 0 → M ω = 0 := by
    filter_upwards [hOffMc, hOffMs, hOffMl] with ω h1 h2 h3 hz
    simp [M, h1 hz, h2 hz, h3 hz]
  have hBound : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
    filter_upwards [hG, hR, hUpper] with ω g r h
    dsimp [M]
    linarith
  have hMeas : MeasurableSet {ω : Ω | σ k ω ≠ 0} :=
    (AvramDividend.Classical.avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k)).compl
  exact AvramDividend.Classical.avram_mix_inf15_supported_mean_zero_event_budget
    {ω : Ω | σ k ω ≠ 0} hMeas (w x) (F k) M (hFI k)
    hMI hMean (by
      filter_upwards [hOff] with ω h hz
      exact h (by simpa only [not_ne_iff] using hz)) hBound
