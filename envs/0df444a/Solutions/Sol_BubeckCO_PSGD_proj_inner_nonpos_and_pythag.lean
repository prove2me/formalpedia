-- Prove2me | solution 1 for BubeckCO.PSGD.proj_inner_nonpos_and_pythag
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:29:03.938852+00:00
-- url     : https://prove2.me/submissions/94e6fdb6-a54e-4927-a1ad-cfc0a2832c9a

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj
set_option autoImplicit false

open BubeckCO.PSGD

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcompact : IsCompact X) (hXconv : Convex ℝ X)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (y p : EuclideanSpace ℝ (Fin n))
    (hp : IsEuclideanProj X y p) :
    inner ℝ (p - x) (p - y) ≤ 0 ∧ ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
  have h_inner : inner ℝ (p - x) (p - y) ≤ 0 := by
    by_contra! h_pos
    have h_quad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        2 * t * inner ℝ (p - x) (p - y) ≤ t ^ 2 * ‖p - x‖ ^ 2 := by
      intro t ht0 ht1
      let z := (1 - t) • p + t • x
      have hz : z ∈ X := hXconv hp.1 hx (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 t)
      have h_le : ‖p - y‖ ≤ ‖z - y‖ := by
        rw [norm_sub_rev p y, norm_sub_rev z y]
        exact hp.2 z hz
      have h_sq : ‖p - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by
        nlinarith [norm_nonneg (p - y), norm_nonneg (z - y)]
      have h_zy : z - y = (p - y) - t • (p - x) := by
        dsimp [z]
        module
      have h_expand : ‖z - y‖ ^ 2 =
          ‖p - y‖ ^ 2 - 2 * (t * inner ℝ (p - x) (p - y)) + (t * ‖p - x‖) ^ 2 := by
        rw [h_zy, norm_sub_sq_real, real_inner_smul_right, real_inner_comm (p - y) (p - x),
          norm_smul, Real.norm_of_nonneg ht0]
      linarith
    let t := min 1 (inner ℝ (p - x) (p - y) / (‖p - x‖ ^ 2 + 1))
    have ht_pos : 0 < t := lt_min zero_lt_one (div_pos h_pos (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht_bound : t * (‖p - x‖ ^ 2 + 1) ≤ inner ℝ (p - x) (p - y) :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hq := h_quad t ht_pos.le ht1
    nlinarith
  refine ⟨h_inner, ?_⟩
  have h_sub : y - x = (p - x) - (p - y) := by abel
  have h_expand : ‖y - x‖ ^ 2 =
      ‖p - x‖ ^ 2 - 2 * inner ℝ (p - x) (p - y) + ‖y - p‖ ^ 2 := by
    rw [h_sub, norm_sub_sq_real, norm_sub_rev p y]
  linarith
