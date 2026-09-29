-- Prove2me | solution 1 for FamousTheorems.hilbert_projection_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:19:21.15281+00:00
-- url     : https://prove2.me/submissions/04281075-43ef-44ed-b7b1-25ecde28f3b7

import Mathlib

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {K : Set F} (hne : K.Nonempty)
    (hc : IsComplete K) (hK : Convex ℝ K) (u : F) : ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hne hc hK u
