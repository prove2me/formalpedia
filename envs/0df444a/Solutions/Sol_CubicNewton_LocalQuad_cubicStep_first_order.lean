-- Prove2me | solution 1 for CubicNewton.LocalQuad.cubicStep_first_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:11:47.847871+00:00
-- url     : https://prove2.me/submissions/41c4f9a7-da03-4770-915e-3710218fb1f3

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.LocalQuad

open scoped RealInnerProductSpace

/-- The Hessian `H x` (derivative of the gradient `g`) is self-adjoint. -/
theorem aux_cso_sym {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  have hf' : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y := by
    intro y
    have := (hf y).hasFDerivAt
    have heq : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (g y)) = innerSL ℝ (g y) := by
      ext w
      simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    rwa [heq] at this
  have hx : HasFDerivAt (fun y => innerSL ℝ (g y)) ((innerSL ℝ).comp (H x)) x :=
    (innerSL ℝ).hasFDerivAt.comp x (hg x)
  have := second_derivative_symmetric hf' hx v w
  simpa using this

end CubicNewton.LocalQuad

open CubicNewton.LocalQuad
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by
  have hsym := aux_cso_sym f g H hf hg x
  have hmin : IsLocalMin (fun y => CubicNewton.Shared.cubicModel g H M x y) T :=
    Filter.Eventually.of_forall (fun y => hT y)
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y - x)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) T := (hasFDerivAt_id T).sub_const x
  have h2 := (innerSL ℝ (g x)).hasFDerivAt.comp T h1
  have h3 := (H x).hasFDerivAt.comp T h1
  have h4 := h3.inner ℝ h1
  have h5 := (hasFDerivAt_norm_rpow (T - x) (by norm_num : (1:ℝ) < 3)).comp T h1
  have h6 := (h2.add (h4.const_mul (1/2 : ℝ))).add (h5.const_mul (M/6))
  have h7 := h6.congr_of_eventuallyEq (f₁ := fun y => CubicNewton.Shared.cubicModel g H M x y)
    (Filter.Eventually.of_forall (fun y => by
      simp only [CubicNewton.Shared.cubicModel, Function.comp, innerSL_apply_apply, Pi.add_apply]
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]))
  have hz := hmin.hasFDerivAt_eq_zero h7
  set v := g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) with hv
  have hw : ∀ w, ⟪v, w⟫ = 0 := by
    intro w
    have := DFunLike.congr_fun hz w
    simp [hv, inner_add_left, inner_smul_left] at this ⊢
    rw [hsym w (T - x)] at this
    have e1 : ‖T - x‖ ^ ((3:ℝ) - 2) = ‖T - x‖ := by norm_num
    simp only [e1, map_sub, inner_sub_left] at this ⊢
    linear_combination this
  exact inner_self_eq_zero.mp (hw v)
