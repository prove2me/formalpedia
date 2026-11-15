-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB31_interior_caplinear_affine_upper_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:36:29.255615+00:00
-- url     : https://prove2.me/submissions/40cc5d77-b3d9-4511-921b-bfdf45297aa6

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b y : ℝ) (hy : b < y) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    deriv V y = 1 ∧ iteratedDeriv 2 V y = 0 := by
  let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
  have hEv : V =ᶠ[𝓝 y] (fun z : ℝ => w b + (z - b)) := by
    filter_upwards [eventually_gt_nhds hy] with z hz
    simp [V, not_le.mpr hz]
  have hlin : (fun z : ℝ => w b + (z - b)) =
      (fun z : ℝ => z + (w b - b)) := by
    funext z
    ring
  rw [hlin] at hEv
  constructor
  · change deriv V y = 1
    rw [hEv.deriv_eq]
    simp [deriv_add_const]
  · have hEq : iteratedDeriv 2 V y =
        deriv (deriv (fun z : ℝ => z + (w b - b))) y := by
        simpa only [iteratedDeriv_succ, iteratedDeriv_one,
          iteratedDeriv_zero] using hEv.deriv.deriv_eq
    simpa [deriv_add_const] using hEq
