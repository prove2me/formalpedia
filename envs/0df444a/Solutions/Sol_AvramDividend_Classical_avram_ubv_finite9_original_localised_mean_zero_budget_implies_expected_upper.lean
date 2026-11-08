-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_localised_mean_zero_budget_implies_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:37:53.167421+00:00
-- url     : https://prove2.me/submissions/9973a0c0-2077-42fe-82a4-a406758d5b6a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_from_exact_cash
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_expectation_DCT

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original stopped mean-zero budgets transfer to local and limiting expectation bounds. -/
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
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
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
        ∂(dividendMeasure D ω)).toReal) :
    ∀ (L : Ω → ℝ),
      (∀ k, AEStronglyMeasurable (F k) P) →
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (L ω))) →
      (∀ k, ∃ M : Ω → ℝ,
        Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, F k ω ≤ w x + M ω)) →
      (∀ k, (∫ ω, F k ω ∂P) ≤ w x) ∧
        (∫ ω, L ω ∂P) ≤ w x  := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro L hFmeas hLim hBudget
  have hFI : ∀ k, Integrable (F k) P :=
    avram_ubv_finite9_original_F_family_integrable_from_exact_cash
      X x q hq C hfinite hxc w hw_cont hw_neg D hD
      τ hCashτI σ hσle F hFsource hFmeas
  have hUpper : ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
    intro k
    obtain ⟨M, hMI, hM0, hFM⟩ := hBudget k
    have hConst : Integrable (fun _ : Ω => w x) P := integrable_const (w x)
    have hMono : (∫ ω, F k ω ∂P) ≤ (∫ ω, w x + M ω ∂P) :=
      integral_mono_ae (hFI k) (hConst.add hMI) hFM
    have hEval : (∫ ω, w x + M ω ∂P) = w x := by
      rw [integral_add hConst hMI]
      simp [hM0]
    calc
      (∫ ω, F k ω ∂P) ≤ (∫ ω, w x + M ω ∂P) := hMono
      _ = w x := hEval
  have hDCT :=
    avram_ubv_finite9_original_F_family_expectation_DCT
      X x q hq C hfinite hxc w hw_cont hw_neg D hD
      τ hCashτI σ hσle F hFsource L hFmeas hLim
  refine ⟨hUpper, ?_⟩
  exact le_of_tendsto hDCT (Filter.Eventually.of_forall hUpper)
