-- Prove2me | solution 1 for AvramDividend.Classical.esscher_convex_positive_shift_right_secant_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:34:29.516284+00:00
-- url     : https://prove2.me/submissions/ddb45f47-ba04-44c3-afdc-f673c85993f2

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set


/-- Interior convexity supplies a finite genuine right-shift secant limit. -/
theorem solution
    (f : ℝ → ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f) :
    Tendsto (fun h : ℝ => (f (φ + h) - f φ) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (derivWithin f (Ioi φ) φ)) := by
  have hi : φ ∈ interior (Ici (0 : ℝ)) := by
    rw [interior_Ici]
    exact hφ
  have hs :
      Tendsto (slope f φ)
        (nhdsWithin φ (Ioi φ \ {φ}))
        (nhds (derivWithin f (Ioi φ) φ)) :=
    hasDerivWithinAt_iff_tendsto_slope.mp
      (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hi)
  have hzero :
      Tendsto (fun h : ℝ => h)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hshift :
      Tendsto (fun h : ℝ => φ + h)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin φ (Ioi φ \ {φ})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero] using hzero.const_add φ
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hz : φ < φ + h := lt_add_of_pos_right φ hh
      exact ⟨hz, by simpa only [mem_singleton_iff] using hz.ne'⟩
  have hlim := hs.comp hshift
  have hfun :
      (fun h : ℝ => (f (φ + h) - f φ) / h) =
      (fun h : ℝ => slope f φ (φ + h)) := by
    funext h
    rw [slope_def_field]
    congr 1
    ring
  rw [hfun]
  exact hlim
