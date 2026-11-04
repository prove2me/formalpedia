-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_monotone_random_future_clock_expected_tail_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:09.077663+00:00
-- url     : https://prove2.me/submissions/67caee65-f20f-4656-ae65-85bfe5816721

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine original future cash expectations converge to zero for
    almost-surely increasing random lower clocks with vanishing pathwise tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : ℕ → Ω → ℝ)
    (hTm : ∀ n, Measurable (T n))
    (hTmono : ∀ᵐ ω ∂P, Monotone (fun n => T n ω))
    (hPoint : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T n ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
        atTop (𝓝 (0 : ℝ≥0∞)))
    (hFinite : dividendValue X q x D < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T n ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T n ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hMeas (n : ℕ) : AEMeasurable (f n) P := by
    simpa only [f] using
      (avram_wave7_03_original_strict_future_random_clock_cash_measurable
        X x D hD q (T n) (hTm n)).aemeasurable
  have hAnti : ∀ᵐ ω ∂P, Antitone (fun n => f n ω) := by
    filter_upwards [hTmono] with ω hω
    intro n m hnm
    dsimp [f]
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt (hω hnm) ht.2⟩
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
  have hLim := lintegral_tendsto_of_tendsto_of_antitone
    hMeas hAnti hFirst.ne (by simpa only [f] using hPoint)
  simpa only [f, lintegral_zero] using hLim
