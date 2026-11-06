-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_cash_finite_grid_two_sided_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:48:56.208198+00:00
-- url     : https://prove2.me/submissions/aacbb4ce-06b8-42b6-a0a6-6bdb60248334

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_lower
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Two-sided original stopped Stieltjes cash grid bound, with each cash
payment discounted exactly once and time-zero mass retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) ∧
    (ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω)))) := by
  exact ⟨
    avram_p3_2_original_finite_stopped_discounted_cash_sum_lower X x D ω q hq T m n,
    avram_p3_2_original_finite_stopped_discounted_cash_sum_upper X x D ω q hq T m n⟩
