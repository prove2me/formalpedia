-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_bv_bounded_real_cash_clock_mean_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:01:26.109365+00:00
-- url     : https://prove2.me/submissions/40f967ae-0ca0-4722-a388-df357ee8d372

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (τ σ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hσMeas : Measurable (fun ω => (σ ω : ℝ)))
    (hτBound : ∀ ω, τ ω ≤ T)
    (hσBound : ∀ ω, σ ω ≤ T)
    (hτσ : ∀ ω, τ ω ≤ σ ω) :
    (∫ ω, (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ω ∂P) ≤
      (∫ ω, (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) ω ∂P) := by
  let fτ : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let fσ : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hIτ : Integrable (fun ω => (fτ ω).toReal) P :=
    avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
      X hX hBV x hx C hxc D hD q hq T τ hτBound hτMeas
  have hIσ : Integrable (fun ω => (fσ ω).toReal) P :=
    avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
      X hX hBV x hx C hxc D hD q hq T σ hσBound hσMeas
  have hσF : ∀ᵐ ω ∂P, fσ ω < ⊤ :=
    avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
      X x C D hD q σ T hσBound
  have hsub (ω : Ω) :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ) := by
    intro t ht
    have hle : (τ ω : ℝ) ≤ (σ ω : ℝ) := by
      exact_mod_cast hτσ ω
    exact ⟨ht.1, le_trans ht.2 hle⟩
  have hmon : ∀ᵐ ω ∂P, (fτ ω).toReal ≤ (fσ ω).toReal := by
    filter_upwards [hσF] with ω hF
    have hpath : fτ ω ≤ fσ ω := lintegral_mono_set (hsub ω)
    exact ENNReal.toReal_mono (ne_of_lt hF) hpath
  exact integral_mono_ae hIτ hIσ hmon
