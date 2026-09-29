-- Prove2me | solution 1 for ConvexOptimization.dualCone_inner_pos_of_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:19.901644+00:00
-- url     : https://prove2.me/submissions/4db5f872-d1ac-46bd-9a6c-9a6c5173244a

import Mathlib
import Definitions.Def_dualCone

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (z w : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ dualCone K) (hzne : z ≠ 0) (hw : w ∈ interior K) :
    0 < ⟪w, z⟫ := by
  have hwK : w ∈ K := interior_subset hw
  have hnonneg : 0 ≤ ⟪w, z⟫ := hz w hwK
  rcases lt_or_eq_of_le hnonneg with h | h
  · exact h
  -- If `⟪w, z⟫ = 0`, move slightly against `z`: still in `K`, but with negative pairing.
  exfalso
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  set δ : ℝ := ε / (2 * ‖z‖) with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : w - δ • z ∈ K := by
    refine interior_subset (hball ?_)
    have : dist (w - δ • z) w = δ * ‖z‖ := by
      rw [dist_eq_norm]
      simp [norm_smul, abs_of_pos hδpos]
    rw [Metric.mem_ball, this, hδ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ‖z‖)]
    nlinarith [mul_pos hε hznorm]
  have := hz _ hmem
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ← h] at this
  nlinarith [this, mul_pos hδpos (pow_pos hznorm 2)]
