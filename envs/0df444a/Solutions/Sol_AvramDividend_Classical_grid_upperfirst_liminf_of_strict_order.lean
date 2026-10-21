-- Prove2me | solution 1 for AvramDividend.Classical.grid_upperfirst_liminf_of_strict_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:00:35.80645+00:00
-- url     : https://prove2.me/submissions/d68d3372-ab88-4a5a-be7d-dfd3bea0e4ad

import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_on_upperfirst
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

/-- The grid upper-first reward liminf equals the continuous reward whenever passage clocks are strictly ordered. -/
theorem solution
    (q : ℝ) (up down : ENNReal)
    (upGrid downGrid : ℕ → ENNReal)
    (hu : Tendsto upGrid atTop (nhds up))
    (hd : Tendsto downGrid atTop (nhds down))
    (hsep : up < down ∨ down < up) :
    (if up < down then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up))) else 0) =
      liminf (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n)))) else 0) atTop := by
  rcases hsep with hupper | hlower
  · have ht :=
      AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_on_upperfirst
        q up down upGrid downGrid hu hd hupper
    simpa only [if_pos hupper] using (Filter.Tendsto.liminf_eq ht).symm
  · have heq :=
      AvramDividend.Classical.chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
        q up down upGrid downGrid hu hd hlower
    have ht : Tendsto
        (fun n => if upGrid n < downGrid n then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n)))) else 0)
        atTop (nhds (0 : ENNReal)) := by
      have hsym : (fun _ : ℕ => (0 : ENNReal)) =ᶠ[atTop]
          (fun n => if upGrid n < downGrid n then
            ENNReal.ofReal (Real.exp
              (-(q * ENNReal.toReal (upGrid n)))) else 0) := by
        filter_upwards [heq] with n hn
        exact hn.symm
      exact tendsto_const_nhds.congr' hsym
    have hnot : ¬ up < down := not_lt_of_ge (le_of_lt hlower)
    simpa only [if_neg hnot] using (Filter.Tendsto.liminf_eq ht).symm
