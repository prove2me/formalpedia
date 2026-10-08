-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:41:40.354869+00:00
-- url     : https://prove2.me/submissions/5d94bb96-9975-4860-8465-f1c2a6ea508d

import Definitions.Def_ConvexOptAlg_SmoothGD_Defs

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

set_option maxHeartbeats 800000

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    |f x - f y - ⟪g y, x - y⟫_ℝ| ≤ β / 2 * ‖x - y‖ ^ 2 := by
  let d := x - y
  let F : ℝ → ℝ := fun t => f (y + t • d) - f y - t * ⟪g y, d⟫_ℝ
  let F' : ℝ → ℝ := fun t => ⟪g (y + t • d) - g y, d⟫_ℝ
  have hF (t : ℝ) : HasDerivAt F (F' t) t := by
    have hline : HasDerivAt (fun s : ℝ => y + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add y
    have hh := (hf.2.1 (y + t • d)).hasFDerivAt.comp_hasDerivAt t hline
    convert (hh.sub_const (f y)).sub ((hasDerivAt_id t).mul_const ⟪g y, d⟫_ℝ) using 1
    all_goals first | rfl | simp [F, F', inner_sub_left]
  have hB (t : ℝ) : HasDerivAt (fun s : ℝ => β / 2 * ‖d‖ ^ 2 * s ^ 2)
      (β * ‖d‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (β / 2 * ‖d‖ ^ 2) using 1
    all_goals first | rfl | (simp only [id_eq, Pi.pow_apply]; ring)
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖F' t‖ ≤ β * ‖d‖ ^ 2 * t := by
    calc
      ‖F' t‖ ≤ ‖g (y + t • d) - g y‖ * ‖d‖ := norm_inner_le_norm _ _
      _ ≤ (β * ‖y + t • d - y‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hf.2.2 _ _) (norm_nonneg _)
      _ = β * ‖d‖ ^ 2 * t := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := F) (f' := F') (a := 0) (b := 1)
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (B := fun s : ℝ => β / 2 * ‖d‖ ^ 2 * s ^ 2)
    (by simp [F]) hB hbound (x := 1) (by norm_num)
  simpa [F, d, Real.norm_eq_abs] using h
