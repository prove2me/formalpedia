-- Prove2me | solution 1 for ConvexOptAlg.CenterGravity.thm_2_1_value_scaled_copy
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T20:01:00.846582+00:00
-- url     : https://prove2.me/submissions/60c8e1bc-c6f0-4e35-8e97-7628bed22153

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace


theorem solution {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : ConvexOptAlg.CenterGravity.IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) :
    f ((1 - ε) • xstar + ε • x) ≤ f xstar + 2 * ε * B := by
  have h1 := hfconv.2 hxstar hx (by linarith : 0 ≤ 1 - ε) hε0 (by ring)
  simp only [smul_eq_mul] at h1
  have h2 := (abs_le.mp (hfB x hx)).2
  have h3 := (abs_le.mp (hfB xstar hxstar)).1
  nlinarith
