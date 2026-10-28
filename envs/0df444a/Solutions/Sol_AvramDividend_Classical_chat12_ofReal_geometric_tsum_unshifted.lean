-- Prove2me | solution 1 for AvramDividend.Classical.chat12_ofReal_geometric_tsum_unshifted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:40:17.469142+00:00
-- url     : https://prove2.me/submissions/714e496a-5ab5-4372-85b4-da97e5e016a1

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

theorem solution (ε p : ℝ)
    (hε : 0 ≤ ε) (hp : 0 ≤ p) :
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ n)) =
      ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by
  have hterm (n : ℕ) :
      ENNReal.ofReal (ε * p ^ n) =
        ENNReal.ofReal ε * (ENNReal.ofReal p) ^ n := by
    rw [ENNReal.ofReal_mul hε, ENNReal.ofReal_pow]
    all_goals exact hp
  calc
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ n)) =
        ∑' n : ℕ, ENNReal.ofReal ε * (ENNReal.ofReal p) ^ n := by
          congr 1
          funext n
          exact hterm n
    _ = ENNReal.ofReal ε *
        (∑' n : ℕ, (ENNReal.ofReal p) ^ n) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by
          rw [ENNReal.tsum_geometric]
