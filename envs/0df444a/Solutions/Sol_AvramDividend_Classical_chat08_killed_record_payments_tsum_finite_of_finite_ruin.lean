-- Prove2me | solution 1 for AvramDividend.Classical.chat08_killed_record_payments_tsum_finite_of_finite_ruin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:28:05.011122+00:00
-- url     : https://prove2.me/submissions/8b597345-7823-4194-a3f2-ea2984907b0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_killed_grid_weights_eventually_zero_of_finite_ruin

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (a b h q : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    (∑' n : ℕ,
      if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (h * Real.exp
          (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
      else 0) < ⊤ := by
  obtain ⟨N, hN⟩ :=
    AvramDividend.Classical.chat08_killed_grid_weights_eventually_zero_of_finite_ruin
      X ω a b h q hh τ hτ
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => hN n (by simpa using hn))]
  refine ENNReal.sum_lt_top.2 fun n _ => ?_
  split_ifs
  · exact ENNReal.ofReal_lt_top
  · exact ENNReal.zero_lt_top
