-- Prove2me | solution 1 for ConvexOptAlg.Ellipsoid.value_scaledCopy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:27:16.618983+00:00
-- url     : https://prove2.me/submissions/41c6cffe-56b4-4417-a0fa-78c4a9ffcda4

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

open ConvexOptAlg.Ellipsoid in
theorem solution {n : ℕ} (X : Set (Fin n → ℝ)) (hX : IsConvexBody X)
    (f : (Fin n → ℝ) → ℝ) (hfcont : ContinuousOn f X) (hf : ConvexOn ℝ X f)
    (B : ℝ) (hfB : ∀ x ∈ X, -B ≤ f x ∧ f x ≤ B)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (xε : Fin n → ℝ) (hxε : xε ∈ scaledCopy X xstar ε) :
    f xε ≤ f xstar + 2 * ε * B := by
  obtain ⟨x, hx, rfl⟩ := hxε
  have h1 := hf.2 hxstar hx (by linarith : (0:ℝ) ≤ 1 - ε) hε0 (by ring)
  have hb1 := hfB x hx
  have hb2 := hfB xstar hxstar
  simp only [smul_eq_mul] at h1
  nlinarith [mul_le_mul_of_nonneg_left hb1.2 hε0, mul_le_mul_of_nonneg_left hb2.1 hε0]
