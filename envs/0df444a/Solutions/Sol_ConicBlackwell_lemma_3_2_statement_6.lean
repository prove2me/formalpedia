-- Prove2me | solution 1 for ConicBlackwell.lemma_3_2_statement_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:59:23.525503+00:00
-- url     : https://prove2.me/submissions/f461dbe6-b1e1-4029-ba34-b8fd70fda56f

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

theorem solution {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) (x y : E (n + 1))
    (hxy : y - x ∈ polar C) :
    Metric.infDist y (polar C) ≤ ‖x‖ := by
  calc Metric.infDist y (polar C) ≤ dist y (y - x) := Metric.infDist_le_dist_of_mem hxy
    _ = ‖x‖ := by rw [dist_eq_norm]; congr 1; abel
