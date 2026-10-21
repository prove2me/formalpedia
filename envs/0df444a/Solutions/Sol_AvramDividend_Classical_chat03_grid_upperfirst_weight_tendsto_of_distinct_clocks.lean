-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:02:56.14701+00:00
-- url     : https://prove2.me/submissions/bfa08618-ebb3-44be-9fbb-b69d69efb4be

import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_on_upperfirst
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped ENNReal

/-!
At distinct limiting passage times the exact upper-first discount
is continuous along convergent grid passage times. The potentially
discontinuous both-infinite tie case is deliberately excluded.
-/
theorem solution
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hne : up ≠ down) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (upGrid n))))
      else 0) atTop
      (𝓝 (if up < down then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
      else 0)) := by
  rcases lt_or_gt_of_ne hne with hupper | hlower
  · simpa [hupper] using
      (chat03_grid_upperfirst_weight_tendsto_on_upperfirst
        q up down upGrid downGrid hu hd hupper)
  · have hzero :=
      chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
        q up down upGrid downGrid hu hd hlower
    have hEq :
        (fun n => if upGrid n < downGrid n then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n))))
        else 0) =ᶠ[atTop]
        (fun _ : ℕ => (0 : ℝ≥0∞)) := hzero
    have hlim : Tendsto
        (fun n => if upGrid n < downGrid n then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop (𝓝 (0 : ℝ≥0∞)) :=
      tendsto_const_nhds.congr' hEq.symm
    have hnot : ¬ up < down := not_lt.mpr (le_of_lt hlower)
    simpa [hnot] using hlim
