-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.eq_3_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:43:27.290968+00:00
-- url     : https://prove2.me/submissions/8467e4b7-d007-475c-87e8-172d89a7e77c

import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_4
import Theorems.Thm_ConvexOptAlg_SmoothGD_lemma_3_5

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    1 / β * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by
  have h1 := lemma_3_5 f g β hβ hf.2.1 (eq_3_4 f g β hconv hf) x y
  have h2 := lemma_3_5 f g β hβ hf.2.1 (eq_3_4 f g β hconv hf) y x
  rw [norm_sub_rev (g y) (g x)] at h2
  rw [show y - x = -(x - y) by abel, inner_neg_right] at h2
  rw [inner_sub_left]
  have he : 1 / β * ‖g x - g y‖ ^ 2 =
      2 * (1 / (2 * β) * ‖g x - g y‖ ^ 2) := by ring
  rw [he]
  linarith
