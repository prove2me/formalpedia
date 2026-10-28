-- Prove2me | solution 1 for AvramDividend.Classical.drained_zero_barrier_truncated_zero_reward_eq_initial_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:27:58.590303+00:00
-- url     : https://prove2.me/submissions/2373816d-d620-46b7-a816-d0567c2a294b

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain_initial_rightLimit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The linear drain is continuous at time zero, so the zero-horizon
    Stieltjes reward remains the exact zero-barrier initial lump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (q : ℝ) (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω)) =
      ENNReal.ofReal x := by
  let B : ℝ≥0 → Ω → ℝ := barrierStrategy X x 0
  let D : ℝ≥0 → Ω → ℝ := fun s ω => B s ω + (s : ℝ)
  have hB : IsDividendStrategy 𝓕 B := by
    exact barrierStrategy_isDividendStrategy_nonnegative_barrier X x 0 hx le_rfl
  have hD : IsDividendStrategy 𝓕 D :=
    dividendStrategy_plus_linear_drain B hB
  have hright : rightLimit D 0 ω = rightLimit B 0 ω :=
    dividendStrategy_plus_linear_drain_initial_rightLimit B hB ω
  have hbar : rightLimit B 0 ω - B 0 ω = x := by
    simpa [B, hx] using
      (barrierStrategy_right_increment_formula X x 0 ω 0)
  calc
    _ = ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
      simpa [D, B] using
        (truncated_dividend_payoff_at_zero_eq_initial_atom D hD q σ ω)
    _ = ENNReal.ofReal x := by
      rw [hright, hD.1 ω]
      simpa [hB.1 ω] using congrArg ENNReal.ofReal hbar
