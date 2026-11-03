-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_stopped_Cash_measurable_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:44:32.945535+00:00
-- url     : https://prove2.me/submissions/3db6f1be-d6d0-48c0-a712-98a166fe5b15

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτBound : ∀ ω, τ ω ≤ T)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    Integrable Cash P ∧ AEStronglyMeasurable Cash P := by
  have hI :=
    avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
      X x C D hD q τ T hτMeas hτBound
  have hEq : Cash = fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal :=
    funext hCash
  rw [← hEq] at hI
  exact ⟨hI, hI.aestronglyMeasurable⟩
