-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_integrable_strict_future_tail_ennreal_eq_ofReal_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:37:21.96607+00:00
-- url     : https://prove2.me/submissions/c3c3c066-da99-444c-be7b-d226cb6c3e5c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Each original future-dividend tail has the exact ENNReal/real integral
    identity, provided the full original signed Stieltjes reward is genuine L1. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    ∀ n : ℕ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  intro n
  have hTailInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ))
      (dividendMeasure D ω) :=
    hInt.mono_set inter_subset_left
  have hPos :
      0 ≤ᵐ[(dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ))]
        (fun t : ℝ => Real.exp (-(q * t))) :=
    Filter.Eventually.of_forall (fun t => (Real.exp_pos (-(q * t))).le)
  exact
    (ofReal_integral_eq_lintegral_ofReal hTailInt hPos).symm
