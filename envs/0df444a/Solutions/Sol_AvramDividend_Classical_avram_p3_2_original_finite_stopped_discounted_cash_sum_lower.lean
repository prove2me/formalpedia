-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_stopped_discounted_cash_sum_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:28:16.447285+00:00
-- url     : https://prove2.me/submissions/f4893cde-34a4-4790-81ea-7ceee8719b18

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_exact_discounted_cash_cell_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original once-discounted physical stopped cash dominates the
sum of right-endpoint discounted unweighted cells, including the
initial right-payment atom exactly once. -/
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
    ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  exact avram_p3_2_original_exact_discounted_cash_cell_lower
    X x D ω q hq T m i
