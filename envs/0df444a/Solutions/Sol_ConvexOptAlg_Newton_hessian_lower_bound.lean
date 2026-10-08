-- Prove2me | solution 1 for ConvexOptAlg.Newton.hessian_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:20:09.181835+00:00
-- url     : https://prove2.me/submissions/44aaf791-8719-42b9-8f8e-65d18e7dd4f0

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

open ConvexOptAlg.Newton in
theorem solution {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (M μ : ℝ) (hM : 0 < M) (hμ : 0 < μ) (hHL : IsLipschitzHessian H M)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hHstar : ∀ v : EuclideanSpace ℝ (Fin n), μ * ‖v‖ ^ 2 ≤ inner ℝ (H xstar v) v)
    (y : EuclideanSpace ℝ (Fin n)) :
    (∀ v : EuclideanSpace ℝ (Fin n),
        inner ℝ (H xstar v) v - M * ‖y - xstar‖ * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v) ∧
    (∀ v : EuclideanSpace ℝ (Fin n), (μ - M * ‖y - xstar‖) * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v) ∧
    (‖y - xstar‖ ≤ μ / (2 * M) →
      ∀ v : EuclideanSpace ℝ (Fin n), μ / 2 * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v) := by
  have h1 : ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ (H xstar v) v - M * ‖y - xstar‖ * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v := by
    intro v
    have hdiff : inner ℝ (H xstar v) v - inner ℝ (H y v) v
        = inner ℝ ((H xstar - H y) v) v := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    have hc : inner ℝ ((H xstar - H y) v) v ≤ ‖(H xstar - H y) v‖ * ‖v‖ :=
      real_inner_le_norm _ _
    have hop : ‖(H xstar - H y) v‖ ≤ ‖H xstar - H y‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hL : ‖H xstar - H y‖ ≤ M * ‖y - xstar‖ := by
      have := hHL xstar y
      rwa [norm_sub_rev xstar y] at this
    have hv : 0 ≤ ‖v‖ := norm_nonneg v
    have h2 : ‖(H xstar - H y) v‖ * ‖v‖ ≤ M * ‖y - xstar‖ * ‖v‖ ^ 2 := by
      calc ‖(H xstar - H y) v‖ * ‖v‖ ≤ (‖H xstar - H y‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right hop hv
        _ ≤ (M * ‖y - xstar‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hv) hv
        _ = M * ‖y - xstar‖ * ‖v‖ ^ 2 := by ring
    linarith
  have h2 : ∀ v : EuclideanSpace ℝ (Fin n),
      (μ - M * ‖y - xstar‖) * ‖v‖ ^ 2 ≤ inner ℝ (H y v) v := by
    intro v
    have := h1 v
    have := hHstar v
    nlinarith
  refine ⟨h1, h2, ?_⟩
  intro hy v
  have hMy : M * ‖y - xstar‖ ≤ μ / 2 := by
    have := mul_le_mul_of_nonneg_left hy hM.le
    rw [show M * (μ / (2 * M)) = μ / 2 by field_simp] at this
    exact this
  have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
  have := h2 v
  have : μ / 2 * ‖v‖ ^ 2 ≤ (μ - M * ‖y - xstar‖) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hv2
  linarith
