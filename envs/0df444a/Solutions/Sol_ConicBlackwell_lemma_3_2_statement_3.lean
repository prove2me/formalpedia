-- Prove2me | solution 1 for ConicBlackwell.lemma_3_2_statement_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:41:22.5272+00:00
-- url     : https://prove2.me/submissions/03149e46-3b12-4aae-acbf-2b71d1a8a42e

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

theorem solution {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) (u : E (n + 1)) (hu : u ∈ C) :
    Metric.infDist u (polar C) = ‖u‖ := by
  have h0 : (0 : E (n + 1)) ∈ polar C := fun x _ => by simp
  apply le_antisymm
  · calc Metric.infDist u (polar C) ≤ dist u 0 := Metric.infDist_le_dist_of_mem h0
      _ = ‖u‖ := dist_zero_right u
  · rw [Metric.le_infDist ⟨0, h0⟩]
    intro θ hθ
    have hin : ⟪θ, u⟫ ≤ 0 := hθ u hu
    rw [dist_eq_norm]
    have hsq : ‖u‖ ^ 2 ≤ ‖u - θ‖ ^ 2 := by
      rw [norm_sub_sq_real]
      nlinarith [real_inner_comm u θ, sq_nonneg ‖θ‖]
    nlinarith [norm_nonneg u, norm_nonneg (u - θ)]
