-- Prove2me | solution 1 for FatkhullinPolyak.HessStep.cubic_taylor_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:32:03.080316+00:00
-- url     : https://prove2.me/submissions/c0a09c75-c5a4-4da7-bd2c-fb6780c5cb31

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem aux_ctb_line {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • y) y t := by
  simpa using ((hasDerivAt_id t).smul_const y).const_add x

theorem aux_ctb_main {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    |f (x + y) - f x - fderiv ℝ f x y - (1 / 2) * fderiv ℝ (fderiv ℝ f) x y y|
      ≤ M / 6 * ‖y‖ ^ 3 := by
  set D2 := fderiv ℝ (fderiv ℝ f) with hD2
  have hA : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • y)) (fderiv ℝ f (x + t • y) y) t := by
    intro t
    exact (hf (x + t • y)).hasFDerivAt.comp_hasDerivAt t (aux_ctb_line x y t)
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (D2 (x + t • y) y y) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y)) (D2 (x + t • y) y) t :=
      (hf' (x + t • y)).hasFDerivAt.comp_hasDerivAt t (aux_ctb_line x y t)
    have h2 := h1.clm_apply (hasDerivAt_const t y)
    simpa using h2
  -- step 1
  set g1 : ℝ → ℝ := fun t => fderiv ℝ f (x + t • y) y - fderiv ℝ f x y - t * D2 x y y with hg1
  have hg1d : ∀ t : ℝ, HasDerivAt g1 (D2 (x + t • y) y y - D2 x y y) t := by
    intro t
    have := ((hB t).sub_const (fderiv ℝ f x y)).sub (hasDerivAt_mul_const (D2 x y y))
    exact this
  have hbound1 : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖D2 (x + t • y) y y - D2 x y y‖ ≤ M * t * ‖y‖ ^ 3 := by
    intro t ht
    have e : D2 (x + t • y) y y - D2 x y y = (D2 (x + t • y) - D2 x) y y := by simp
    rw [e]
    calc ‖(D2 (x + t • y) - D2 x) y y‖ ≤ ‖D2 (x + t • y) - D2 x‖ * ‖y‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ (M * ‖x + t • y - x‖) * ‖y‖ * ‖y‖ := by
          gcongr
          exact hM _ _
      _ = M * t * ‖y‖ ^ 3 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
          ring
  have hBd1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => M / 2 * t ^ 2 * ‖y‖ ^ 3) (M * t * ‖y‖ ^ 3) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (M / 2)).mul_const (‖y‖ ^ 3)
    refine this.congr_deriv ?_
    push_cast; ring
  have step1 : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖g1 t‖ ≤ M / 2 * t ^ 2 * ‖y‖ ^ 3 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t _ => (hg1d t).continuousAt.continuousWithinAt)
      (fun t _ => (hg1d t).hasDerivWithinAt) ?_ hBd1 hbound1
    simp [hg1]
  -- step 2
  set φ : ℝ → ℝ := fun t => f (x + t • y) - f x - t * fderiv ℝ f x y
    - t ^ 2 / 2 * D2 x y y with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ (g1 t) t := by
    intro t
    have := (((hA t).sub_const (f x)).sub (hasDerivAt_mul_const (fderiv ℝ f x y))).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (D2 x y y))
    refine this.congr_deriv ?_
    simp only [hg1]; push_cast; ring
  have hBd2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => M / 6 * t ^ 3 * ‖y‖ ^ 3)
      (M / 2 * t ^ 2 * ‖y‖ ^ 3) t := by
    intro t
    have := ((hasDerivAt_pow 3 t).const_mul (M / 6)).mul_const (‖y‖ ^ 3)
    refine this.congr_deriv ?_
    push_cast; ring
  have step2 : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖φ t‖ ≤ M / 6 * t ^ 3 * ‖y‖ ^ 3 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t _ => (hφd t).continuousAt.continuousWithinAt)
      (fun t _ => (hφd t).hasDerivWithinAt) ?_ hBd2
      (fun t ht => step1 t (Set.Ico_subset_Icc_self ht))
    simp [hφ]
  have := step2 1 ⟨zero_le_one, le_rfl⟩
  simp only [hφ, one_smul, one_mul, one_pow, mul_one, Real.norm_eq_abs] at this
  convert this using 2

end FatkhullinPolyak.HessStep

open FatkhullinPolyak.HessStep

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      |f (x + y) - f x - inner ℝ (gradient f x) y - (1 / 2) * hessQuad f x y| ≤ M / 6 * ‖y‖ ^ 3 := by
  intro x y
  have h := aux_ctb_main f M hf hf' hM x y
  have e : inner ℝ (gradient f x) y = fderiv ℝ f x y := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [e]
  exact h
