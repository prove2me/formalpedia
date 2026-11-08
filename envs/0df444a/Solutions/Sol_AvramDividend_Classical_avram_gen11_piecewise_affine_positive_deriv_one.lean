-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen11_piecewise_affine_positive_deriv_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:43:51.534199+00:00
-- url     : https://prove2.me/submissions/42f1eebe-ae75-45bf-b146-a214f3e5db85

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

/-- The positive-reserve germ of the discontinuous-at-ruin payoff has slope one. -/
theorem solution
    (x : ℝ) (hx : 0 < x) :
    deriv (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x = 1 := by
  have heq : (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) =ᶠ[𝓝 x]
      (fun u : ℝ => 1 + u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
    exact if_neg (not_lt.mpr (le_of_lt hu))
  rw [heq.deriv_eq]
  simpa using (deriv_const_add_id (x := x) (1 : ℝ))
