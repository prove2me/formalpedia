-- Prove2me | solution 1 for ConvexAnalysis.exists_transverse_interior_center
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:23.40196+00:00
-- url     : https://prove2.me/submissions/4fbd1a95-3078-4b5a-ac95-b48d7a676cf7

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (K : Set Phase)
    (h0 : (0 : Phase) ∈ interior K) (H : Phase →L[ℝ] ℝ) (hH : H ≠ 0)
    (y : Phase) : ∃ z ∈ interior K, H (y - z) ≠ 0 := by
  by_contra! hn
  have hyzero : H y = 0 := by simpa using hn 0 h0
  have hmax : IsLocalMax H 0 := by
    filter_upwards [isOpen_interior.mem_nhds h0] with z hz
    have hz0 : H z = 0 := by
      have h := hn z hz
      rw [map_sub, hyzero] at h
      linarith
    simp only [hz0, map_zero, le_refl]
  exact hH (hmax.hasFDerivAt_eq_zero H.hasFDerivAt)
