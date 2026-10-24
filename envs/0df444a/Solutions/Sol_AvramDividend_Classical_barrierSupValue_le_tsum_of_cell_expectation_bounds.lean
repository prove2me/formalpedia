-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_tsum_of_cell_expectation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:02:24.694516+00:00
-- url     : https://prove2.me/submissions/5a5a787b-9c04-4b9a-ae5f-6d5e2023ecb5

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards_unconditional
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Bound actual stopped reflection dividends by any summable cellwise upper budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0)
    (f : ℕ → ℝ≥0∞)
    (hf : ∀ i : ℕ,
      (∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) ≤ f i) :
    barrierSupValue X a q ≤ (∑' i, f i) := by
  rw [barrierSupValue_eq_sum_expected_partition_rewards_unconditional
    X a q hq u hu hcofinal hstart]
  exact ENNReal.tsum_le_tsum hf
