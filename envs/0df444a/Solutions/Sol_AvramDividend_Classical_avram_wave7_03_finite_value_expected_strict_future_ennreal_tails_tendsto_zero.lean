-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_value_expected_strict_future_ennreal_tails_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:12:37.739775+00:00
-- url     : https://prove2.me/submissions/734f376d-6497-4139-9f59-28c8404e810d

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_implies_ae_ENNReal_strict_future_tails_zero_direct

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite true expected original dividendValue forces the expected genuine
    future ENNReal Stieltjes cash itself to converge to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hMeas (n : ℕ) : AEMeasurable (f n) P := by
    simpa only [f] using
      (avram_wave7_03_original_strict_future_random_clock_cash_measurable
        X x D hD q (fun _ => (n : ℝ)) measurable_const).aemeasurable
  have hAnti : ∀ᵐ ω ∂P, Antitone (fun n => f n ω) := by
    filter_upwards [] with ω
    intro n m hnm
    dsimp [f]
    apply lintegral_mono_set
    intro t ht
    have hnmReal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hmt : (m : ℝ) < t := ht.2
    exact ⟨ht.1, lt_of_le_of_lt hnmReal hmt⟩
  have hFirst : (∫⁻ ω, f 0 ω ∂P) < ⊤ := by
    have hLe : (∫⁻ ω, f 0 ω ∂P) ≤ dividendValue X q x D := by
      change (∫⁻ ω, f 0 ω ∂P) ≤
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      apply lintegral_mono
      intro ω
      apply lintegral_mono_set
      intro t ht
      exact ht.1
    exact lt_of_le_of_lt hLe hFinite
  have hPoint : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [f] using
      (avram_wave7_03_finite_original_value_implies_ae_ENNReal_strict_future_tails_zero_direct
        X x D hD q hFinite)
  have hLim := lintegral_tendsto_of_tendsto_of_antitone
    hMeas hAnti hFirst.ne hPoint
  simpa only [f, lintegral_zero] using hLim
