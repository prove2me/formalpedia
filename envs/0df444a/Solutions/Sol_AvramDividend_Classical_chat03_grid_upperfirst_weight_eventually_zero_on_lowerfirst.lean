-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:05:48.641219+00:00
-- url     : https://prove2.me/submissions/166ad567-2094-4560-a2ea-85ac2461d0ff

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

/-! The upper-first grid payoff is eventually zero when the lower clock wins strictly. -/
theorem solution
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hlower : down < up) :
    ∀ᶠ n in atTop,
      (if upGrid n < downGrid n then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (upGrid n))))
      else 0) = 0 := by
  have hsep : ∀ᶠ n in atTop, downGrid n < upGrid n :=
    Filter.Tendsto.eventually_lt hd hu hlower
  filter_upwards [hsep] with n hn
  simp only [if_neg (not_lt.mpr (le_of_lt hn))]
