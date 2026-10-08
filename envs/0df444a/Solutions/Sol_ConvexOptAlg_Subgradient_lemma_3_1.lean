-- Prove2me | solution 1 for ConvexOptAlg.Subgradient.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T18:52:13.238447+00:00
-- url     : https://prove2.me/submissions/0e1b58c4-93de-488d-9928-de2e8044cd45

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs
import Theorems.Thm_ConvexOptimization_projection_iff_obtuse_angle

open scoped RealInnerProductSpace

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X)
    (x y p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection X y p) :
    ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
  have hvar : ⟪y - p, x - p⟫ ≤ 0 :=
    (ConvexOptimization.projection_iff_obtuse_angle X hXconv y p hp.1).mp
      (fun w hw => by simpa [dist_eq_norm] using hp.2 w hw) x hx
  have h1 : y - x = (y - p) + (p - x) := by abel
  have h2 : ⟪y - p, p - x⟫ = -⟪y - p, x - p⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  have h3 : ‖y - x‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * ⟪y - p, p - x⟫ + ‖p - x‖ ^ 2 := by
    rw [h1, norm_add_sq_real]
  rw [h3, h2]
  nlinarith [hvar]
