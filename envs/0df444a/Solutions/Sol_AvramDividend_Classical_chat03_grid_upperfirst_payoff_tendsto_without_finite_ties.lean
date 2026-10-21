-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:15:55.181757+00:00
-- url     : https://prove2.me/submissions/2dc5e079-bac1-4a17-b5be-7f81358d16a6

import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
Complete upper-first grid-discount convergence when the only possible
tie is both-infinite and the sampled upper clock preserves non-exit.
-/
theorem solution
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hfiniteTie : up = down → up = ∞)
    (hNoUpGrid : up = ∞ → ∀ n : ℕ, upGrid n = ∞) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop
      (𝓝 (if up < down then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal up)))
        else 0)) := by
  by_cases hne : up ≠ down
  · exact chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks
      q up down upGrid downGrid hu hd hne
  · have heq : up = down := not_ne_iff.mp hne
    have hinf : up = ∞ := hfiniteTie heq
    have hgrid := hNoUpGrid hinf
    have hzero :
        (fun n => if upGrid n < downGrid n then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n))))
          else 0) = fun _ : ℕ => (0 : ℝ≥0∞) := by
      funext n
      simp [hgrid n]
    have htarget :
        (if up < down then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal up)))
          else 0) = (0 : ℝ≥0∞) := by
      rw [heq]
      simp
    rw [hzero, htarget]
    exact tendsto_const_nhds
