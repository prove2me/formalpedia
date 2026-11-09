-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_original_condexp_reward_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T21:45:26.131187+00:00
-- url     : https://prove2.me/submissions/1f20e8b2-5206-498a-b95d-c4eeebad49aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_stopped_C2_ito_domination_witness

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
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
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
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (F k) ω ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨M, hMI, hCentred, hDom⟩ :=
    avram_ubv_finite12_original_stopped_C2_ito_domination_witness
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ F hσstop hσle hFsource hFI k
  have hconstI : Integrable (fun _ : Ω => w x) P := integrable_const _
  have hsumI : Integrable (fun ω : Ω => w x + M ω) P :=
    hconstI.add hMI
  have hCondDom :
      (condExp (𝓕.rightCont 0) P (F k)) ≤ᵐ[P]
        (condExp (𝓕.rightCont 0) P
          (fun ω : Ω => w x + M ω)) := by
    first
    | exact condExp_mono (m := 𝓕.rightCont 0) (hFI k) hsumI hDom
    | exact condExp_mono (hFI k) hsumI hDom
    | exact condExp_mono (𝓕.rightCont 0) (hFI k) hsumI hDom
  have hm : 𝓕.rightCont 0 ≤ mΩ := (𝓕.rightCont).le 0
  have hCondSum :=
    condExp_add hconstI hMI (𝓕.rightCont 0)
  filter_upwards [hCondDom, hCondSum, hCentred]
    with ω hle heq hz
  calc
    condExp (𝓕.rightCont 0) P (F k) ω ≤
        condExp (𝓕.rightCont 0) P
          (fun ω : Ω => w x + M ω) ω := hle
    _ = condExp (𝓕.rightCont 0) P (fun _ : Ω => w x) ω +
          condExp (𝓕.rightCont 0) P M ω := by
        change condExp (𝓕.rightCont 0) P
          ((fun _ : Ω => w x) + M) ω = _
        exact heq
    _ = w x := by
        rw [congrFun (condExp_const (μ := P) hm (w x)) ω, hz]
        ring
