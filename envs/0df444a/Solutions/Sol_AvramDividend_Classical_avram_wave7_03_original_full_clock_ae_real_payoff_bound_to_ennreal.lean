-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_clock_ae_real_payoff_bound_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:51:05.577844+00:00
-- url     : https://prove2.me/submissions/4cc8b09f-ebb9-4083-9629-f08a0a920796

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Transfer an almost-sure real domination of the genuine complete
    stopped Stieltjes payout to an ENNReal outer integral inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ)
    (G : Ω → ℝ)
    (hPath : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ≤ G ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)
  have hFinite : ∀ᵐ ω ∂P, F ω < ⊤ := by
    simpa only [F] using
      (avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
        X x C D hD T hT q)
  have hReal : ∀ᵐ ω ∂P, (F ω).toReal ≤ G ω := by
    simpa only [F] using hPath
  change (∫⁻ ω, F ω ∂P) ≤ ∫⁻ ω, ENNReal.ofReal (G ω) ∂P
  apply lintegral_mono_ae
  filter_upwards [hFinite, hReal] with ω hω hB
  calc
    F ω = ENNReal.ofReal ((F ω).toReal) :=
      (ENNReal.ofReal_toReal (ne_of_lt hω)).symm
    _ ≤ ENNReal.ofReal (G ω) := ENNReal.ofReal_le_ofReal hB
