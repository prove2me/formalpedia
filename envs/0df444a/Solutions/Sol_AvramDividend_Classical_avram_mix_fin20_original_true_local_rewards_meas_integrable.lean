-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin20_original_true_local_rewards_meas_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:59:55.904223+00:00
-- url     : https://prove2.me/submissions/e225d25e-a629-4dab-963f-53c268b4ddc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_from_exact_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDsource : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) (hCfinite : C ≠ ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσkstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σk k ω : WithTop ℝ≥0)))
    (hσkle : ∀ k ω, σk k ω ≤ σ ω)
    (Fk : ℕ → Ω → ℝ)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    (∀ k, Measurable (Fk k)) ∧
    (∀ k, Integrable (Fk k) P) := by
  classical
  have hCashI :=
    avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q σ hσstop F hFsource hFI
  have hMeas (k : ℕ) : Measurable (Fk k) :=
    avram_ubv_top9_original_any_clock_source_reward_measurable
      X x q w hw_cont hw_neg D hDsource
      (σk k) (hσkstop k) (Fk k) (hFksource k)
  have hAE (k : ℕ) : AEStronglyMeasurable (Fk k) P :=
    (hMeas k).aestronglyMeasurable
  have hInt :=
    avram_ubv_finite9_original_F_family_integrable_from_exact_cash
      X x q hq C hCfinite hxc w hw_cont hw_neg
      D hD σ hCashI σk hσkle Fk hFksource hAE
  exact ⟨hMeas, hInt⟩
