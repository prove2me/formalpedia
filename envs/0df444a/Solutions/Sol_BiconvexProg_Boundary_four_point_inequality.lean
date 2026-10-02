-- Prove2me | solution 1 for BiconvexProg.Boundary.four_point_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:36:10.444717+00:00
-- url     : https://prove2.me/submissions/1f4896a2-5114-402b-b515-6029870df294

import Mathlib
import Definitions.Def_BiconvexProg_Boundary_BiconcaveOn

open BiconvexProg.Boundary in
theorem solution {p q : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)))
    (φ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) → ℝ) (hφ : BiconcaveOn S φ)
    (xstar s : EuclideanSpace ℝ (Fin p)) (ystar t : EuclideanSpace ℝ (Fin q))
    (h₁ : ∀ x ∈ segment ℝ xstar s, (x, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) ∈ S)
    (h₂ : ∀ y ∈ segment ℝ ystar t, (xstar, y) ∈ S)
    (h₃ : ∀ y ∈ segment ℝ ystar t, (s, y) ∈ S) :
    (1 / 2 : ℝ) * φ (xstar, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) +
        (1 / 2 : ℝ) * φ (s, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) ≤
      φ ((1 / 2 : ℝ) • (xstar, ystar) + (1 / 2 : ℝ) • (s, t)) ∧
    (1 / 4 : ℝ) * (φ (xstar, ystar) + φ (xstar, t) + φ (s, ystar) + φ (s, t)) ≤
      (1 / 2 : ℝ) * φ (xstar, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) +
        (1 / 2 : ℝ) * φ (s, (1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) := by
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hs : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  constructor
  · have hc := hφ.1 ((1 / 2 : ℝ) • ystar + (1 / 2 : ℝ) • t) (segment ℝ xstar s)
      (convex_segment xstar s) h₁
    have := hc.2 (left_mem_segment ℝ xstar s) (right_mem_segment ℝ xstar s) hh hh hs
    simp only [smul_eq_mul] at this
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk]
    exact this
  · have hc2 := hφ.2 xstar (segment ℝ ystar t) (convex_segment ystar t) h₂
    have hc3 := hφ.2 s (segment ℝ ystar t) (convex_segment ystar t) h₃
    have a2 := hc2.2 (left_mem_segment ℝ ystar t) (right_mem_segment ℝ ystar t) hh hh hs
    have a3 := hc3.2 (left_mem_segment ℝ ystar t) (right_mem_segment ℝ ystar t) hh hh hs
    simp only [smul_eq_mul] at a2 a3
    linarith
