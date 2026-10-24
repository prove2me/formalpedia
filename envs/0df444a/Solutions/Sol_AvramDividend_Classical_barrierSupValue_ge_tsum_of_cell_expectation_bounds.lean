-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_tsum_of_cell_expectation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:02:20.851268+00:00
-- url     : https://prove2.me/submissions/de41531b-3759-433e-b316-f2b7d2171682

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards_unconditional
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Dominate a countable renewal reward budget by actual stopped dividend rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0)
    (f : ℕ → ℝ≥0∞)
    (hf : ∀ i : ℕ, f i ≤
      (∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P)) :
    (∑' i, f i) ≤ barrierSupValue X a q := by
  rw [barrierSupValue_eq_sum_expected_partition_rewards_unconditional
    X a q hq u hu hcofinal hstart]
  exact ENNReal.tsum_le_tsum hf
