-- Prove2me | solution 1 for DynamicsRelativity.angularMomentum_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T00:32:10.450985+00:00
-- url     : https://prove2.me/submissions/d9cc1199-44cb-4429-be52-ff05e8fa79b5

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

/-
  We prove that the angular momentum L = m (x × v) is orthogonal to both x and v.
  This is the scalar triple product identity: (a × b) · a = 0 and (a × b) · b = 0.
-/

theorem solution (m : ℝ) (x : ℝ → Vec) (t : ℝ) :
    inner ℝ (angularMomentum m x t) (x t) = 0 ∧
      inner ℝ (angularMomentum m x t) (vel x t) = 0 := by
  unfold angularMomentum cross vel
  constructor
  · simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    suffices h : @inner ℝ Vec _ (WithLp.toLp 2 (crossProduct (x t).ofLp (deriv x t).ofLp)) (x t) = 0 by
      rw [h, mul_zero]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dot_self_cross _ _
  · simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    suffices h : @inner ℝ Vec _ (WithLp.toLp 2 (crossProduct (x t).ofLp (deriv x t).ofLp)) (deriv x t) = 0 by
      rw [h, mul_zero]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dot_cross_self _ _
