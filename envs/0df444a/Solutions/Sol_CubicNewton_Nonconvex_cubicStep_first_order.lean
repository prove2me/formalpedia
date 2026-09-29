-- Prove2me | solution 1 for CubicNewton.Nonconvex.cubicStep_first_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:35:49.474426+00:00
-- url     : https://prove2.me/submissions/5a466764-bda3-4d80-bc5d-231b3356e72e

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

theorem aux_csfo_symm {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hF_convex : Convex ℝ F) (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  have h1 : ∀ y ∈ interior F, HasFDerivAt f (innerSL ℝ (g y)) y := fun y hy => by
    have := (hf y (interior_subset hy)).hasFDerivAt
    have e : innerSL ℝ (g y) = InnerProductSpace.toDual ℝ _ (g y) := by
      ext z; simp [InnerProductSpace.toDual_apply_apply]
    rw [e]; exact this
  have h2 : HasFDerivWithinAt (fun y => innerSL ℝ (g y)) ((innerSL ℝ).comp (H x))
      (interior F) x :=
    ((innerSL ℝ).hasFDerivAt.comp x (hg x hx)).hasFDerivWithinAt
  have := hF_convex.second_derivative_within_at_symmetric hF_int h1 hx h2 v w
  simpa using this

end CubicNewton.Nonconvex

open CubicNewton.Nonconvex
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by
  set h := T - x with hh
  set w := g x + H x h + (1 / 2 * M * ‖h‖) • h with hw
  have hl : HasDerivAt (fun t : ℝ => T + t • w - x) w 0 := by
    have := (((hasDerivAt_id (0:ℝ)).smul_const w).const_add T).sub_const x
    simpa using this
  have e0 : T + (0:ℝ) • w - x = h := by simp [hh]
  have h1 : HasDerivAt (fun t : ℝ => ⟪g x, T + t • w - x⟫) ⟪g x, w⟫ 0 := by
    have := (hasDerivAt_const (0:ℝ) (g x)).inner ℝ hl
    simpa using this
  have hHl : HasDerivAt (fun t : ℝ => H x (T + t • w - x)) (H x w) 0 :=
    (H x).hasFDerivAt.comp_hasDerivAt 0 hl
  have h2 : HasDerivAt (fun t : ℝ => ⟪H x (T + t • w - x), T + t • w - x⟫)
      (⟪H x h, w⟫ + ⟪H x w, h⟫) 0 := by
    have := hHl.inner ℝ hl
    rw [e0] at this
    exact this
  have h3 : HasDerivAt (fun t : ℝ => ‖T + t • w - x‖ ^ 3) (3 * ‖h‖ * ⟪h, w⟫) 0 := by
    have := (hasFDerivAt_norm_rpow (T + (0:ℝ) • w - x) (p := 3) (by norm_num)).comp_hasDerivAt
      0 hl
    rw [e0] at this
    have e3 : (fun t : ℝ => ‖T + t • w - x‖ ^ 3) = (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ (3:ℝ)) ∘
        (fun t : ℝ => T + t • w - x) := by
      funext t
      simp only [Function.comp_apply]
      exact_mod_cast rfl
    rw [e3]
    refine this.congr_deriv ?_
    rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    norm_num
  have hψ : HasDerivAt (fun t : ℝ => CubicNewton.Shared.cubicModel g H M x (T + t • w))
      (⟪g x, w⟫ + 1 / 2 * (⟪H x h, w⟫ + ⟪H x w, h⟫) + M / 6 * (3 * ‖h‖ * ⟪h, w⟫)) 0 := by
    unfold CubicNewton.Shared.cubicModel
    exact (h1.add (h2.const_mul (1 / 2))).add (h3.const_mul (M / 6))
  have hmin : IsLocalMin (fun t : ℝ => CubicNewton.Shared.cubicModel g H M x (T + t • w)) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [zero_smul, add_zero]
    exact hT _
  have hzero := hmin.hasDerivAt_eq_zero hψ
  have hs := aux_csfo_symm F f g H hF_convex hF_int hf hg x hx w h
  rw [hs] at hzero
  have hww : ⟪w, w⟫ = 0 := by
    have : ⟪w, w⟫ = ⟪g x, w⟫ + ⟪H x h, w⟫ + 1 / 2 * M * ‖h‖ * ⟪h, w⟫ := by
      conv_lhs => rw [hw]
      rw [inner_add_left, inner_add_left, real_inner_smul_left]
    rw [this]
    linarith
  exact inner_self_eq_zero.mp hww
