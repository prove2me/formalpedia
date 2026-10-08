-- Prove2me | solution 1 for ConvexOptAlg.ProjectedGD.eq_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:22.9542+00:00
-- url     : https://prove2.me/submissions/58a7e4f1-9a65-43f7-9f5f-b2fb9d8e0651

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

lemma a8a8021b_varineq {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcv : Convex ℝ X)
    (u p : EuclideanSpace ℝ (Fin n)) (hp : IsMetricProjection X u p) :
    ∀ w ∈ X, ⟪u - p, w - p⟫_ℝ ≤ 0 := by
  obtain ⟨hpX, hmin⟩ := hp
  refine (norm_eq_iInf_iff_real_inner_le_zero hXcv hpX).1 ?_
  have : Nonempty X := ⟨⟨p, hpX⟩⟩
  apply le_antisymm
  · refine le_ciInf ?_
    intro w
    have := hmin w w.2
    simpa [dist_eq_norm] using this
  · have hb : BddBelow (Set.range fun w : X => ‖u - (w : EuclideanSpace ℝ (Fin n))‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hb ⟨p, hpX⟩

open OnlineConvexOpt.FirstOrder ConvexOptAlg.ProjectedGD in open scoped InnerProductSpace in
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (x y xplus : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hy : y ∈ X)
    (hplus : IsMetricProjection X (x - β⁻¹ • g x) xplus) :
    ⟪g x, xplus - y⟫_ℝ ≤ ⟪gradMap β x xplus, xplus - y⟫_ℝ := by
  have hv := a8a8021b_varineq X hXcv _ _ hplus y hy
  have key : gradMap β x xplus - g x = β • ((x - β⁻¹ • g x) - xplus) := by
    unfold gradMap
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul]
    abel
  have h2 : ⟪gradMap β x xplus - g x, xplus - y⟫_ℝ ≥ 0 := by
    rw [key, real_inner_smul_left]
    have : ⟪(x - β⁻¹ • g x) - xplus, xplus - y⟫_ℝ = -⟪(x - β⁻¹ • g x) - xplus, y - xplus⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    rw [this]
    nlinarith
  rw [inner_sub_left] at h2
  linarith
