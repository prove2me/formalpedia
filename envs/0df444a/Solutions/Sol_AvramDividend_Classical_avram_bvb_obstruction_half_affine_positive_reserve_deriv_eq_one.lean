-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:17:31.440306+00:00
-- url     : https://prove2.me/submissions/4e2219ac-fd58-4214-9612-2a787d571b94

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Real Set
open scoped Topology
theorem solution (y : ℝ) (hy : 0 < y) :
    deriv (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u) y = 1 := by
  have hev : (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u) =ᶠ[𝓝 y]
      (fun u : ℝ => u + 1 / 2) := by
    apply Filter.Eventually.mono (isOpen_Ioi.mem_nhds hy)
    intro u hu
    have hnot : ¬ u < 0 := not_lt.mpr (le_of_lt hu)
    simp only [hnot, if_false]
    ring
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hd : HasDerivAt (fun u : ℝ => u + (1 / 2 : ℝ)) 1 y := by
    simpa only [id_eq] using ((hasDerivAt_id y).add_const (1 / 2 : ℝ))
  exact hd.deriv
