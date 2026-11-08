-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_F_family_integrable_from_exact_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:10:58.203307+00:00
-- url     : https://prove2.me/submissions/214ce90a-c62a-4120-95d8-5397806453ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Integrability for every exact original finite-cap stopped value-plus-cash payoff. -/
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
    (∀ k, AEStronglyMeasurable (F k) P) →
    ∀ k, Integrable (F k) P  := by
  classical
  intro hFmeas k
  obtain ⟨B, hB, hBound, hEnvI⟩ :=
    avram_ubv_finite9_original_F_family_integrable_envelope
      X x q hq C hfinite hxc w hw_cont hw_neg D hD
      τ hCashτI σ hσle F hFsource
  apply hEnvI.mono (hFmeas k)
  filter_upwards [] with ω
  have hnn : 0 ≤ B +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := add_nonneg hB ENNReal.toReal_nonneg
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using hBound k ω
