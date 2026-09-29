-- Prove2me | solution 1 for CubicNewton.GradDom.cubicStep_first_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:25:15.122238+00:00
-- url     : https://prove2.me/submissions/08c90c4c-69fb-4e30-9b0e-2cc357dc2426

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Symmetry of `H y` at interior points of `F`. -/
theorem aux_cfo_symm_int {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ interior F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H y v, w⟫ = ⟪v, H y w⟫ := by
  have hev : ∀ᶠ z in nhds y,
      HasFDerivAt f (innerSL ℝ (g z) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) z := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    have h0 := (hf z (interior_subset hz)).hasFDerivAt
    have he : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (g z)
        = (innerSL ℝ (g z) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
      ext u; simp [InnerProductSpace.toDual_apply_apply]
    rw [he] at h0
    exact h0
  have hd : HasFDerivAt (fun z => (innerSL ℝ (g z) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp
        (H y)) y :=
    (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.comp
      y (hg y (interior_subset hy))
  have := second_derivative_symmetric_of_eventually hev hd v w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply] at this
  rw [this, real_inner_comm]

theorem aux_cfo_symm {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪v, H x w⟫ := by
  have hH : ContinuousOn H F := by
    have : LipschitzOnWith (Real.toNNReal L) H F :=
      LipschitzOnWith.of_dist_le' (fun a ha b hb => by
        rw [dist_eq_norm, dist_eq_norm]; exact hLip a ha b hb)
    exact this.continuousOn
  have h1 : ContinuousOn (fun z => ⟪H z v, w⟫) F := by fun_prop
  have h2 : ContinuousOn (fun z => ⟪v, H z w⟫) F := by fun_prop
  have heq : Set.EqOn (fun z => ⟪H z v, w⟫) (fun z => ⟪v, H z w⟫) (interior F) :=
    fun z hz => aux_cfo_symm_int F f g H hf hg z hz v w
  have hcl : F ⊆ closure (interior F) := by
    rw [hF_convex.closure_interior_eq_closure_of_nonempty_interior hF_int, hF_closed.closure_eq]
  exact heq.of_subset_closure h1 h2 interior_subset hcl hx

end CubicNewton.GradDom

open CubicNewton.GradDom
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
  have hsym := aux_cfo_symm F f g H L hF_closed hF_convex hF_int hf hg hLip x hx
  -- derivative of the cubic model at T
  have hlin : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y - x)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) T :=
    (hasFDerivAt_id T).sub_const x
  have h1 := (hasFDerivAt_const (g x) T).inner ℝ hlin
  have h2 := ((H x).hasFDerivAt.comp T hlin).inner ℝ hlin
  have h3 := (hasFDerivAt_norm_rpow (T - x) (by norm_num : (1:ℝ) < 3)).comp T hlin
  have h3' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y - x‖ ^ 3)
      ((((3:ℝ) * ‖T - x‖ ^ ((3:ℝ) - 2)) • innerSL ℝ (T - x)).comp
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) T := by
    have : ((fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (3:ℝ)) ∘ fun y => y - x)
        = (fun y : EuclideanSpace ℝ (Fin n) => ‖y - x‖ ^ 3) := by
      funext y; simp only [Function.comp_apply]; exact_mod_cast Real.rpow_natCast ‖y - x‖ 3
    rw [← this]; exact h3
  have hφ := (h1.add (h2.const_mul (1/2))).add (h3'.const_mul (M / 6))
  have hmin : IsLocalMin (fun y => CubicNewton.Shared.cubicModel g H M x y) T :=
    Filter.Eventually.of_forall (fun y => hT y)
  have hzero := hmin.hasFDerivAt_eq_zero (by
    unfold CubicNewton.Shared.cubicModel; exact hφ)
  have key : ∀ u, ⟪g x, u⟫ + 1 / 2 * (⟪H x (T - x), u⟫ + ⟪H x u, T - x⟫)
      + M / 6 * (3 * ‖T - x‖ ^ ((3:ℝ) - 2) * ⟪T - x, u⟫) = 0 := by
    intro u
    have := congrArg (fun φ => φ u) hzero
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id', id_eq,
      innerSL_apply_apply, smul_eq_mul, inner_zero_left, zero_add,
      ContinuousLinearMap.zero_apply] at this
    linarith
  set h := T - x
  set v := g x + H x h + (1 / 2 * M * ‖h‖) • h with hvdef
  have hk := key v
  rw [hsym v h, real_inner_comm (H x h) v] at hk
  have hr : ‖h‖ ^ ((3:ℝ) - 2) = ‖h‖ := by norm_num
  rw [hr] at hk
  have hvv : ⟪v, v⟫ = 0 := by
    have e : ⟪v, v⟫ = ⟪g x, v⟫ + ⟪H x h, v⟫ + (1 / 2 * M * ‖h‖) * ⟪h, v⟫ := by
      nth_rewrite 1 [hvdef]
      rw [inner_add_left, inner_add_left, real_inner_smul_left]
    rw [e]; linear_combination hk
  exact inner_self_eq_zero.mp hvv
