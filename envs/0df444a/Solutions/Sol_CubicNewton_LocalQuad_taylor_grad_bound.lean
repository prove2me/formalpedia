-- Prove2me | solution 1 for CubicNewton.LocalQuad.taylor_grad_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:52:10.232525+00:00
-- url     : https://prove2.me/submissions/44caf21d-c49e-4c6c-9df4-6c97460d224c

import Mathlib

namespace CubicNewton.LocalQuad

end CubicNewton.LocalQuad

open CubicNewton.LocalQuad

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by
  intro x y
  set d := y - x with hd
  let φ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => g (x + t • d) - t • H x d - g x
  let φ' : ℝ → EuclideanSpace ℝ (Fin n) := fun t => H (x + t • d) d - H x d
  have hderiv : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 : HasDerivAt (fun t : ℝ => g (x + t • d)) (H (x + t • d) d) t :=
      (hg (x + t • d)).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • H x d) (H x d) t := by
      simpa using (hasDerivAt_id t).smul_const (H x d)
    exact (h2.sub h3).sub_const (g x)
  let B : ℝ → ℝ := fun t => 1 / 2 * L * ‖d‖ ^ 2 * t ^ 2
  let B' : ℝ → ℝ := fun t => L * ‖d‖ ^ 2 * t
  have hB : ∀ t, HasDerivAt B (B' t) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (1 / 2 * L * ‖d‖ ^ 2))
    refine this.congr_deriv ?_
    simp only [B']
    norm_num
    ring
  have hcont : ContinuousOn φ (Set.Icc 0 1) :=
    fun t _ => (hderiv t).continuousAt.continuousWithinAt
  have hφ' : ∀ t ∈ Set.Ico (0:ℝ) 1, HasDerivWithinAt φ (φ' t) (Set.Ici t) t :=
    fun t _ => (hderiv t).hasDerivWithinAt
  have ha : ‖φ 0‖ ≤ B 0 := by simp [φ, B]
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1, ‖φ' t‖ ≤ B' t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have e : φ' t = (H (x + t • d) - H x) d := by simp [φ']
    rw [e]
    calc ‖(H (x + t • d) - H x) d‖ ≤ ‖H (x + t • d) - H x‖ * ‖d‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖x + t • d - x‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
      _ = B' t := by
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, B']
          ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hφ' ha hB hbound
    (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by simp)
  have e1 : φ 1 = g y - g x - H x (y - x) := by
    simp only [φ, one_smul, hd, add_sub_cancel]
    abel
  rw [e1] at key
  simp only [B, one_pow, mul_one] at key
  exact key
