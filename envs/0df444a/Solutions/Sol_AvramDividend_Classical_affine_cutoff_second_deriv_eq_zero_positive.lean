-- Prove2me | solution 1 for AvramDividend.Classical.affine_cutoff_second_deriv_eq_zero_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:21:15.177221+00:00
-- url     : https://prove2.me/submissions/ffdf8d24-2fa1-4790-8a34-2421dfdd1651

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology

/-- The zero-extended affine candidate has vanishing second derivative
    throughout the strictly positive reserve region. -/
theorem solution (y : ℝ) (hy : 0 < y) :
    iteratedDeriv 2 (fun z : ℝ => if z < 0 then 0 else z - 1) y = 0 := by
  let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
  have hderiv_ev :
      (deriv w) =ᶠ[𝓝 y] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact AvramDividend.Classical.affine_cutoff_deriv_eq_one_positive z hz
  have hsecond : deriv (deriv w) y = 0 := by
    rw [hderiv_ev.deriv_eq]
    simp
  simpa [w, iteratedDeriv_succ, iteratedDeriv_zero] using hsecond
