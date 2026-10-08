-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:43:25.666362+00:00
-- url     : https://prove2.me/submissions/41f21791-1b5f-4af7-b1a9-fc37761e620e

import Definitions.Def_ConvexOptAlg_SmoothGD_Defs

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (h34 : ∀ x y : EuclideanSpace ℝ (Fin n),
      0 ≤ f x - f y - ⟪g y, x - y⟫_ℝ ∧ f x - f y - ⟪g y, x - y⟫_ℝ ≤ β / 2 * ‖x - y‖ ^ 2)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x - f y ≤ ⟪g x, x - y⟫_ℝ - 1 / (2 * β) * ‖g x - g y‖ ^ 2 := by
  let d := g x - g y
  let z := y + (1 / β) • d
  have hzx : z - x = -(x - y) + (1 / β) • d := by dsimp [z]; module
  have hzy : z - y = (1 / β) • d := by dsimp [z]; abel
  have h1 := (h34 z x).1
  have h2 := (h34 z y).2
  rw [hzx, inner_add_right, inner_neg_right, real_inner_smul_right] at h1
  rw [hzy, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hβ)] at h2
  have hi : ⟪g x, d⟫_ℝ - ⟪g y, d⟫_ℝ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq d
  have he : β / 2 * (1 / β * ‖d‖) ^ 2 = 1 / (2 * β) * ‖d‖ ^ 2 := by
    field_simp
    <;> ring
  rw [he] at h2
  change f x - f y ≤ ⟪g x, x - y⟫_ℝ - 1 / (2 * β) * ‖d‖ ^ 2
  have hi' : 1 / β * (⟪g x, d⟫_ℝ - ⟪g y, d⟫_ℝ) =
      2 * (1 / (2 * β) * ‖d‖ ^ 2) := by rw [hi]; ring
  linarith
