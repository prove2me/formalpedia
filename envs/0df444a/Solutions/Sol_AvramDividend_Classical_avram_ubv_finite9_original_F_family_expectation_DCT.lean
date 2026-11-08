-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_F_family_expectation_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:10:50.437821+00:00
-- url     : https://prove2.me/submissions/9f05488e-ae33-418e-bb73-22c080448628

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

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
      Tendsto (fun k => ∫ ω, F k ω ∂P) atTop (𝓝 (∫ ω, L ω ∂P))  := by
  classical
  intro L hFmeas hLim
  obtain ⟨B, hB, hBound, hBI⟩ :=
    avram_ubv_finite9_original_F_family_integrable_envelope
      X x q hq C hfinite hxc w hw_cont hw_neg D hD
      τ hCashτI σ hσle F hFsource
  have hNormBound : ∀ k, ∀ᵐ ω ∂P,
      ‖F k ω‖ ≤ B +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
    intro k
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hBound k ω
  exact tendsto_integral_of_dominated_convergence
    (fun ω => B +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    hFmeas hBI hNormBound hLim
