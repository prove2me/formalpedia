-- Prove2me | solution 1 for FiniteEnergyPlane.hasDerivAt_im_conj_mul_of_eigenEq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:43:27.89733+00:00
-- url     : https://prove2.me/submissions/e3a9c96c-352a-49c7-920b-84e11948da13

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add



namespace FiniteEnergyPlane

theorem hasDerivAt_im_conj_mul_of_eigenEq_aux (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ t, (S t).IsSymm) {μ₁ μ₂ : ℝ} {x y : ℝ → CauchyRiemannIndex.Vec 1}
    (hx : Differentiable ℝ x)
    (hxe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x t)) -
      Matrix.toEuclideanLin (S t) (x t) = μ₁ • x t)
    (hy : Differentiable ℝ y)
    (hye : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv y t)) -
      Matrix.toEuclideanLin (S t) (y t) = μ₂ • y t) (t : ℝ) :
    HasDerivAt (fun s => (starRingEnd ℂ (vecToC (x s)) * vecToC (y s)).im)
      ((μ₂ - μ₁) * (starRingEnd ℂ (vecToC (x t)) * vecToC (y t)).re) t := by
  have comp : ∀ {μ : ℝ} {e : ℝ → CauchyRiemannIndex.Vec 1}, Differentiable ℝ e →
      (∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv e t)) -
        Matrix.toEuclideanLin (S t) (e t) = μ • e t) → ∀ t : ℝ,
      HasDerivAt (fun s => e s (Sum.inl 0))
        (-(S t (Sum.inr 0) (Sum.inl 0) * e t (Sum.inl 0) +
          S t (Sum.inr 0) (Sum.inr 0) * e t (Sum.inr 0)) - μ * e t (Sum.inr 0)) t ∧
      HasDerivAt (fun s => e s (Sum.inr 0))
        (S t (Sum.inl 0) (Sum.inl 0) * e t (Sum.inl 0) +
          S t (Sum.inl 0) (Sum.inr 0) * e t (Sum.inr 0) + μ * e t (Sum.inl 0)) t := by
    intro μ e hd' hE' t
    have hd : HasDerivAt e (deriv e t) t := (hd' t).hasDerivAt
    have hL := (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1)).hasFDerivAt.comp_hasDerivAt t hd
    have hR := (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1)).hasFDerivAt.comp_hasDerivAt t hd
    have hE := hE' t
    have eL := congrArg (fun v : CauchyRiemannIndex.Vec 1 => v (Sum.inl 0)) hE
    have eR := congrArg (fun v : CauchyRiemannIndex.Vec 1 => v (Sum.inr 0)) hE
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.J, Matrix.fromBlocks] at eL eR
    simp [Function.comp_def] at hL hR
    exact ⟨hL.congr_deriv (by linarith), hR.congr_deriv (by linarith)⟩
  obtain ⟨a₁, b₁⟩ := comp hx hxe t
  obtain ⟨a₂, b₂⟩ := comp hy hye t
  have hsym : S t (Sum.inr 0) (Sum.inl 0) = S t (Sum.inl 0) (Sum.inr 0) :=
    (hS t).apply (Sum.inl 0) (Sum.inr 0)
  have hfun : (fun s => (starRingEnd ℂ (vecToC (x s)) * vecToC (y s)).im) =
      fun s => x s (Sum.inl 0) * y s (Sum.inr 0) - x s (Sum.inr 0) * y s (Sum.inl 0) := by
    funext s
    simp [vecToC]
    ring
  rw [hfun]
  refine (HasDerivAt.sub (HasDerivAt.mul a₁ b₂) (HasDerivAt.mul b₁ a₂)).congr_deriv ?_
  simp only [vecToC, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [hsym]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ t, (S t).IsSymm) {μ₁ μ₂ : ℝ} {x y : ℝ → CauchyRiemannIndex.Vec 1}
    (hx : Differentiable ℝ x)
    (hxe : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv x t)) -
      Matrix.toEuclideanLin (S t) (x t) = μ₁ • x t)
    (hy : Differentiable ℝ y)
    (hye : ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv y t)) -
      Matrix.toEuclideanLin (S t) (y t) = μ₂ • y t) (t : ℝ) :
    HasDerivAt (fun s => (starRingEnd ℂ (vecToC (x s)) * vecToC (y s)).im)
      ((μ₂ - μ₁) * (starRingEnd ℂ (vecToC (x t)) * vecToC (y t)).re) t :=
  hasDerivAt_im_conj_mul_of_eigenEq_aux S hS hx hxe hy hye t
