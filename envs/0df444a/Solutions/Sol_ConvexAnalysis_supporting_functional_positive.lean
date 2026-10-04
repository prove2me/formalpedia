-- Prove2me | solution 1 for ConvexAnalysis.supporting_functional_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T18:40:49.254981+00:00
-- url     : https://prove2.me/submissions/351d6d42-3932-4d4e-b070-160b0780641a

import Mathlib.Analysis.Calculus.LocalExtr.Basic
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E)
    (h0 : (0 : E) ∈ interior K) (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (y : E) (hsupport : ∀ x ∈ K, L x ≤ L y) : 0 < L y := by
  have hnonneg : 0 ≤ L y := by simpa using hsupport 0 (interior_subset h0)
  have hne : L y ≠ 0 := by
    intro heq
    have hmax : IsLocalMax L 0 := by
      filter_upwards [mem_interior_iff_mem_nhds.mp h0] with x hx
      simpa only [map_zero, heq] using hsupport x hx
    exact hL (hmax.hasFDerivAt_eq_zero L.hasFDerivAt)
  exact lt_of_le_of_ne hnonneg hne.symm
