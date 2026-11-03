-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_integrable_strict_future_ENNReal_stieltjes_tails_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:38:01.973212+00:00
-- url     : https://prove2.me/submissions/833cbc48-505f-44a1-abb4-7fe06dd71571

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine signed original pre-ruin L1 gives actual future ENNReal cash tails
    vanishing on exactly the same dividend Stieltjes measure. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by
  have hTailReal :=
    avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
      X x D ω q hInt
  have hEq (n : ℕ) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
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
  have hLim :
      Tendsto (fun n : ℕ => ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)))
        atTop (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
    (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hTailReal
  simpa only [hEq, ENNReal.ofReal_zero] using hLim
