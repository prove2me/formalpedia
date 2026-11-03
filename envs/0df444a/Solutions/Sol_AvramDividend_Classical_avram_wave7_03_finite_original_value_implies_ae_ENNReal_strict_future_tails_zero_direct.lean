-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_ENNReal_strict_future_tails_zero_direct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:38:10.192433+00:00
-- url     : https://prove2.me/submissions/beaf448f-8aea-4617-903f-4b6b51fa5fba

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- From finite genuine expected payout to almost surely vanishing exact
    original ENNReal strict-future Stieltjes payment tails. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
        atTop (𝓝 0) := by
  have hAeCash : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    ((avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
      X x D hD q).mp hFinite).2
  filter_upwards [hAeCash] with ω hω
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω) :=
    ((avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
      X x D hD ω q).mp hω)
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
        (dividendMeasure D ω) := hInt.mono_set inter_subset_left
    have hPos :
        0 ≤ᵐ[(dividendMeasure D ω).restrict
          (paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ))]
          (fun t : ℝ => Real.exp (-(q * t))) :=
      Filter.Eventually.of_forall (fun t => (Real.exp_pos (-(q * t))).le)
    exact (ofReal_integral_eq_lintegral_ofReal hTailInt hPos).symm
  have hLim :
      Tendsto (fun n : ℕ => ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)))
        atTop (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
    (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hTailReal
  simpa only [hEq, ENNReal.ofReal_zero] using hLim
