-- Prove2me | solution 1 for FiniteEnergyPlane.hasDerivAt_im_conj_mul_loopEigen
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:04:15.947309+00:00
-- url     : https://prove2.me/submissions/c837ab17-506a-48a4-9fd7-f34b15477447

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add



namespace FiniteEnergyPlane

open scoped ContDiff

theorem hasDerivAt_im_conj_mul_loopEigen_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) {μ₁ μ₂ : ℝ}
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (h₁ : IsLoopEigen Sinf μ₁ e₁)
    (h₂ : IsLoopEigen Sinf μ₂ e₂) (t : ℝ) :
    HasDerivAt (fun s => (starRingEnd ℂ (vecToC (e₁ s)) * vecToC (e₂ s)).im)
      ((μ₂ - μ₁) * (starRingEnd ℂ (vecToC (e₁ t)) * vecToC (e₂ t)).re) t := by
  have comp : ∀ {μ : ℝ} {e : ℝ → CauchyRiemannIndex.Vec 1}, IsLoopEigen Sinf μ e → ∀ t : ℝ,
      HasDerivAt (fun s => e s (Sum.inl 0))
        (-(Sinf t (Sum.inr 0) (Sum.inl 0) * e t (Sum.inl 0) +
          Sinf t (Sum.inr 0) (Sum.inr 0) * e t (Sum.inr 0)) - μ * e t (Sum.inr 0)) t ∧
      HasDerivAt (fun s => e s (Sum.inr 0))
        (Sinf t (Sum.inl 0) (Sum.inl 0) * e t (Sum.inl 0) +
          Sinf t (Sum.inl 0) (Sum.inr 0) * e t (Sum.inr 0) + μ * e t (Sum.inl 0)) t := by
    intro μ e he t
    have hd : HasDerivAt e (deriv e t) t :=
      ((he.1.differentiable (by simp)) t).hasDerivAt
    have hL := (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1)).hasFDerivAt.comp_hasDerivAt t hd
    have hR := (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1)).hasFDerivAt.comp_hasDerivAt t hd
    have hE := he.2.2.2 t
    have eL := congrArg (fun v : CauchyRiemannIndex.Vec 1 => v (Sum.inl 0)) hE
    have eR := congrArg (fun v : CauchyRiemannIndex.Vec 1 => v (Sum.inr 0)) hE
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.J, Matrix.fromBlocks] at eL eR
    simp [Function.comp_def] at hL hR
    exact ⟨hL.congr_deriv (by linarith), hR.congr_deriv (by linarith)⟩
  obtain ⟨a₁, b₁⟩ := comp h₁ t
  obtain ⟨a₂, b₂⟩ := comp h₂ t
  have hsym : Sinf t (Sum.inr 0) (Sum.inl 0) = Sinf t (Sum.inl 0) (Sum.inr 0) :=
    (hSinf.2.2 t).apply (Sum.inl 0) (Sum.inr 0)
  have hfun : (fun s => (starRingEnd ℂ (vecToC (e₁ s)) * vecToC (e₂ s)).im) =
      fun s => e₁ s (Sum.inl 0) * e₂ s (Sum.inr 0) - e₁ s (Sum.inr 0) * e₂ s (Sum.inl 0) := by
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

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) {μ₁ μ₂ : ℝ}
    {e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1} (h₁ : IsLoopEigen Sinf μ₁ e₁)
    (h₂ : IsLoopEigen Sinf μ₂ e₂) (t : ℝ) :
    HasDerivAt (fun s => (starRingEnd ℂ (vecToC (e₁ s)) * vecToC (e₂ s)).im)
      ((μ₂ - μ₁) * (starRingEnd ℂ (vecToC (e₁ t)) * vecToC (e₂ t)).re) t :=
  hasDerivAt_im_conj_mul_loopEigen_aux Sinf hSinf h₁ h₂ t
