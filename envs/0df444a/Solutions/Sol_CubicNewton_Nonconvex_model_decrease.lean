-- Prove2me | solution 1 for CubicNewton.Nonconvex.model_decrease
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:46:56.001615+00:00
-- url     : https://prove2.me/submissions/a9be92c8-05ad-4e61-a5f2-8af6f3cb4d04

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

theorem aux_md_model_line {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x h : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    CubicNewton.Shared.cubicModel g H M x (x + t • h) =
      t * ⟪g x, h⟫ + 1 / 2 * (t ^ 2 * ⟪H x h, h⟫) + M / 6 * (|t| ^ 3 * ‖h‖ ^ 3) := by
  unfold CubicNewton.Shared.cubicModel
  have e : x + t • h - x = t • h := by abel
  rw [e, inner_smul_right, map_smul, inner_smul_left, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow]
  simp only [conj_trivial]
  ring

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
    f x - (f x + CubicNewton.Shared.cubicModel g H M x T) ≥ M / 12 * ‖x - T‖ ^ 3 := by
  have hT1 : CubicNewton.Shared.cubicModel g H M x T =
      ⟪g x, T - x⟫ + 1 / 2 * ⟪H x (T - x), T - x⟫ + M / 6 * ‖T - x‖ ^ 3 := rfl
  have key : ∀ t : ℝ, CubicNewton.Shared.cubicModel g H M x T ≤
      t * ⟪g x, T - x⟫ + 1 / 2 * (t ^ 2 * ⟪H x (T - x), T - x⟫)
        + M / 6 * (|t| ^ 3 * ‖T - x‖ ^ 3) := by
    intro t
    rw [← aux_md_model_line]
    exact hT _
  rw [hT1] at key
  rw [hT1, norm_sub_rev x T]
  generalize ⟪g x, T - x⟫ = a at key ⊢
  generalize ⟪H x (T - x), T - x⟫ = b at key ⊢
  generalize ‖T - x‖ = r at key ⊢
  have ha : a ≤ 0 := by
    have := key (-1)
    norm_num at this
    linarith
  let p : ℝ → ℝ := fun t => t * a + 1 / 2 * (t ^ 2 * b) + M / 6 * (t ^ 3 * r ^ 3)
  have hmin : IsLocalMin p 1 := by
    have hnhds : Set.Ioi (0:ℝ) ∈ nhds (1:ℝ) := Ioi_mem_nhds one_pos
    filter_upwards [hnhds] with t ht
    have := key t
    rw [abs_of_pos (Set.mem_Ioi.mp ht)] at this
    simp only [p]
    linarith
  have hderiv : HasDerivAt p (a + b + M / 2 * r ^ 3) 1 := by
    have h1 := ((hasDerivAt_id (1:ℝ)).mul_const a).add
      ((((hasDerivAt_pow 2 (1:ℝ)).mul_const b).const_mul (1 / 2)).add
        (((hasDerivAt_pow 3 (1:ℝ)).mul_const (r ^ 3)).const_mul (M / 6)))
    have hfun : p = ((fun y : ℝ => id y * a) + ((fun y : ℝ => 1 / 2 * (y ^ 2 * b)) +
        fun y : ℝ => M / 6 * (y ^ 3 * r ^ 3))) := by
      funext t; simp only [p, id, Pi.add_apply]; ring
    rw [hfun]
    exact h1.congr_deriv (by norm_num; ring)
  have hD := hmin.hasDerivAt_eq_zero hderiv
  nlinarith
