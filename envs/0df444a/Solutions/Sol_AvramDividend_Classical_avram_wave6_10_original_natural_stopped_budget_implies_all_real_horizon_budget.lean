-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:47:25.024635+00:00
-- url     : https://prove2.me/submissions/27537e2a-f6c3-4310-8a6b-9cab336e66d4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform budgets on natural stopped ruin clocks control every closed
    real-time dividend horizon, preserving its terminal payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (A : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A) :
    ∀ T : ℝ, 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A := by
  intro T hT
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt hT hn
  have hsub (ω : Ω) :
      paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
    have heq :
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) =
          paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ) := by
      simpa using (paymentTimes_min_ofReal_eq_inter_Iio_of_pos
        (ruinTime X x D ω) (n : ℝ) hnpos)
    rw [heq]
    rintro t ⟨htpay, htT⟩
    exact ⟨htpay, lt_of_le_of_lt htT hn⟩
  have hmono (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    MeasureTheory.lintegral_mono_set (hsub ω)
  exact (MeasureTheory.lintegral_mono hmono).trans (hBound n)
