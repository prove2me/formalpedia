-- Prove2me | solution 1 for CubicNewton.Nonconvex.taylor_grad_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:31.54459+00:00
-- url     : https://prove2.me/submissions/add499c4-8e24-4f3b-9f80-b90b5b45843a

import Mathlib

open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F, ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by
  intro x hx y hy
  have hseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • (y - x) ∈ F := by
    intro t ht
    have h1 : x + t • (y - x) = (1 - t) • x + t • y := by module
    rw [h1]
    exact hF_convex hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hderivAll : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => g (x + s • (y - x)) - (g x + s • (H x (y - x))))
        ((H (x + t • (y - x))) (y - x) - (H x) (y - x)) t := by
    intro t ht
    have hmem := hseg t ht
    have hline : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have hcomp : HasDerivAt (fun s : ℝ => g (x + s • (y - x)))
        ((H (x + t • (y - x))) (y - x)) t :=
      (hg _ hmem).comp_hasDerivAt t hline
    have hlin2 : HasDerivAt (fun s : ℝ => g x + s • (H x (y - x))) ((H x) (y - x)) t := by
      simpa using ((hasDerivAt_id t).smul_const ((H x) (y - x))).const_add (g x)
    exact hcomp.sub hlin2
  have hcont : ContinuousOn (fun s : ℝ => g (x + s • (y - x)) - (g x + s • (H x (y - x))))
      (Set.Icc (0 : ℝ) 1) := fun t ht => ((hderivAll t ht).continuousAt).continuousWithinAt
  have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 1 / 2 * L * ‖y - x‖ ^ 2 * s ^ 2)
      (L * ‖y - x‖ ^ 2 * t) t := by
    intro t
    have h2 : HasDerivAt (fun s : ℝ => 1 / 2 * L * ‖y - x‖ ^ 2 * s ^ 2)
        (1 / 2 * L * ‖y - x‖ ^ 2 * ((2 : ℕ) * t ^ (2 - 1))) t :=
      (hasDerivAt_pow 2 t).const_mul _
    have heq : 1 / 2 * L * ‖y - x‖ ^ 2 * ((2 : ℕ) * t ^ (2 - 1)) = L * ‖y - x‖ ^ 2 * t := by
      push_cast; ring
    rw [← heq]
    exact h2
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖(H (x + t • (y - x))) (y - x) - (H x) (y - x)‖ ≤ L * ‖y - x‖ ^ 2 * t := by
    intro t ht
    have hmem := hseg t ⟨ht.1, ht.2.le⟩
    have hsub : (H (x + t • (y - x))) (y - x) - (H x) (y - x)
        = (H (x + t • (y - x)) - H x) (y - x) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [hsub]
    have h1 : ‖(H (x + t • (y - x)) - H x) (y - x)‖
        ≤ ‖H (x + t • (y - x)) - H x‖ * ‖y - x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖H (x + t • (y - x)) - H x‖ ≤ L * ‖x + t • (y - x) - x‖ :=
      hLip _ hmem _ hx
    have h3 : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [h3] at h2
    calc ‖(H (x + t • (y - x)) - H x) (y - x)‖
        ≤ ‖H (x + t • (y - x)) - H x‖ * ‖y - x‖ := h1
      _ ≤ (L * (t * ‖y - x‖)) * ‖y - x‖ := by
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = L * ‖y - x‖ ^ 2 * t := by ring
  have ha : ‖(fun s : ℝ => g (x + s • (y - x)) - (g x + s • (H x (y - x)))) 0‖
      ≤ (fun s : ℝ => 1 / 2 * L * ‖y - x‖ ^ 2 * s ^ 2) 0 := by
    simp
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun t ht => (hderivAll t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) ha hB hbound
    (Set.right_mem_Icc.mpr zero_le_one)
  simp only [one_smul, one_pow, mul_one] at hmain
  have hxy : x + (y - x) = y := by module
  rw [hxy] at hmain
  calc ‖g y - g x - H x (y - x)‖ = ‖g y - (g x + H x (y - x))‖ := by
        rw [sub_sub]
    _ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := hmain
