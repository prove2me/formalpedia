-- Prove2me | solution 1 for CubicNewton.GradDom.grad_norm_at_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:05:39.529984+00:00
-- url     : https://prove2.me/submissions/7a58b2e5-5135-4abe-be16-ba66b50fd9a2

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Symmetry of the Hessian at interior points. -/
theorem aux_gnas_symm_int {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ interior F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H y v, w⟫ = ⟪H y w, v⟫ := by
  set I : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) with hI
  have h1 : ∀ᶠ z in nhds y, HasFDerivAt f (I (g z)) z := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hy] with z hz
    have := (hf z hz).hasFDerivAt
    have e : I (g z) = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (g z) := by
      ext u
      rw [InnerProductSpace.toDual_apply_apply]
      rfl
    rw [e]
    exact this
  have h2 : HasFDerivAt (fun z => I (g z)) (I.comp (H y)) y :=
    I.hasFDerivAt.comp y (hg y (interior_subset hy))
  have := second_derivative_symmetric_of_eventually h1 h2 v w
  exact this

/-- Symmetry of the Hessian at every point of `F` (by density of the interior). -/
theorem aux_gnas_symm {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  have hHc : ContinuousOn H F := by
    have : LipschitzOnWith (Real.toNNReal L) H F :=
      LipschitzOnWith.of_dist_le' (fun a ha b hb => by
        rw [dist_eq_norm, dist_eq_norm]; exact hLip a ha b hb)
    exact this.continuousOn
  have hc1 : ContinuousOn (fun y => ⟪H y v, w⟫) F :=
    (hHc.clm_apply continuousOn_const).inner continuousOn_const
  have hc2 : ContinuousOn (fun y => ⟪H y w, v⟫) F :=
    (hHc.clm_apply continuousOn_const).inner continuousOn_const
  have hsub : F ⊆ closure (interior F) := by
    rw [hF_convex.closure_interior_eq_closure_of_nonempty_interior hF_int, hF_closed.closure_eq]
  have := Set.EqOn.of_subset_closure (f := fun y => ⟪H y v, w⟫) (g := fun y => ⟪H y w, v⟫)
    (fun y hy => aux_gnas_symm_int F f g H hf hg y hy v w) hc1 hc2 interior_subset hsub
  exact this hx

/-- First-order optimality condition for the cubic model. -/
theorem aux_gnas_foc {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hsym : ∀ v w, ⟪H x v, w⟫ = ⟪H x w, v⟫)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (M / 2 * ‖T - x‖) • (T - x) = 0 := by
  set h := T - x with hh
  set w := g x + H x h + (M / 2 * ‖h‖) • h with hw
  let u : ℝ → EuclideanSpace ℝ (Fin n) := fun t => (T + t • w) - x
  have hu : HasDerivAt u w 0 := by
    have := (((hasDerivAt_id' (0:ℝ)).smul_const w).const_add T).sub_const x
    exact this.congr_deriv (by simp)
  have hu0 : u 0 = h := by simp [u, hh]
  have d1 : HasDerivAt (fun t => ⟪g x, u t⟫) ⟪g x, w⟫ 0 := by
    have := (hasDerivAt_const (0:ℝ) (g x)).inner ℝ hu
    simpa using this
  have d2 : HasDerivAt (fun t => ⟪H x (u t), u t⟫) (⟪H x h, w⟫ + ⟪H x w, h⟫) 0 := by
    have := ((H x).hasFDerivAt.comp_hasDerivAt (0:ℝ) hu).inner ℝ hu
    refine this.congr_deriv ?_
    simp only [Function.comp_apply, hu0]
  have d3 : HasDerivAt (fun t => ‖u t‖ ^ 3) (3 * ‖h‖ * ⟪h, w⟫) 0 := by
    have := (hasFDerivAt_norm_rpow (u 0) (by norm_num : (1:ℝ) < 3)).comp_hasDerivAt (0:ℝ) hu
    have e : ((fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (3:ℝ)) ∘ u) = (fun t => ‖u t‖ ^ 3) := by
      funext t
      simp only [Function.comp_apply]
      exact_mod_cast Real.rpow_natCast ‖u t‖ 3
    rw [e] at this
    refine this.congr_deriv ?_
    rw [hu0, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    norm_num
  have hd : HasDerivAt (fun t : ℝ => CubicNewton.Shared.cubicModel g H M x (T + t • w))
      (⟪g x, w⟫ + 1 / 2 * (⟪H x h, w⟫ + ⟪H x w, h⟫) + M / 6 * (3 * ‖h‖ * ⟪h, w⟫)) 0 := by
    have := (d1.add (d2.const_mul (1 / 2))).add (d3.const_mul (M / 6))
    exact this
  have hmin : IsLocalMin (fun t : ℝ => CubicNewton.Shared.cubicModel g H M x (T + t • w)) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [zero_smul, add_zero]
    exact hT _
  have h0 := hmin.hasDerivAt_eq_zero hd
  have hww : ⟪w, w⟫ = 0 := by
    rw [hsym w h] at h0
    have : ⟪w, w⟫ = ⟪g x, w⟫ + ⟪H x h, w⟫ + (M / 2 * ‖h‖) * ⟪h, w⟫ := by
      conv_lhs => rw [hw]
      rw [inner_add_left, inner_add_left, real_inner_smul_left]
    rw [this]
    linear_combination h0
  exact inner_self_eq_zero.1 hww

/-- Second-order Taylor bound for the gradient. -/
theorem aux_gnas_taylor {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F) :
    ‖g T - g x - H x (T - x)‖ ≤ L / 2 * ‖T - x‖ ^ 2 := by
  set h := T - x with hh
  let γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => g (x + t • h) - g x - t • H x h
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • h ∈ F := fun t ht =>
    hF_convex.add_smul_sub_mem hx hTF ht
  have hγ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ (H (x + t • h) h - H x h) t := by
    intro t ht
    have h1 := (hg _ (hmem t ht)).comp_hasDerivAt t
      (((hasDerivAt_id' t).smul_const h).const_add x)
    have h2 := (h1.sub_const (g x)).sub ((hasDerivAt_id' t).smul_const (H x h))
    exact h2.congr_deriv (by simp)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := γ)
    (f' := fun t => H (x + t • h) h - H x h) (B := fun t => L / 2 * ‖h‖ ^ 2 * t ^ 2)
    (B' := fun t => L * ‖h‖ ^ 2 * t)
    (fun t ht => (hγ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hγ t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [γ])
    (fun t => by
      have := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖h‖ ^ 2)
      refine this.congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      show ‖H (x + t • h) h - H x h‖ ≤ L * ‖h‖ ^ 2 * t
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(H (x + t • h) - H x) h‖ ≤ ‖H (x + t • h) - H x‖ * ‖h‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖x + t • h - x‖ * ‖h‖ := by
            gcongr
            exact hLip _ (hmem t (Set.Ico_subset_Icc_self ht)) x hx
        _ = L * ‖h‖ ^ 2 * t := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]; ring)
  have := key (Set.right_mem_Icc.2 zero_le_one)
  simpa [γ, hh] using this

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
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖g T‖ ≤ 1 / 2 * (L + M) * ‖x - T‖ ^ 2 := by
  have hsym := aux_gnas_symm F f g H L hF_closed hF_convex hF_int hf hg hLip x hx
  have hfoc := aux_gnas_foc g H M x T hsym hT
  have htay := aux_gnas_taylor F g H L hF_convex hg hLip x T hx hTF
  have e : g T = (g T - g x - H x (T - x)) - (M / 2 * ‖T - x‖) • (T - x) := by
    rw [← sub_eq_zero]
    rw [show g T - ((g T - g x - H x (T - x)) - (M / 2 * ‖T - x‖) • (T - x))
        = g x + H x (T - x) + (M / 2 * ‖T - x‖) • (T - x) by abel]
    exact hfoc
  rw [e, norm_sub_rev x T]
  calc ‖(g T - g x - H x (T - x)) - (M / 2 * ‖T - x‖) • (T - x)‖
      ≤ ‖g T - g x - H x (T - x)‖ + ‖(M / 2 * ‖T - x‖) • (T - x)‖ := norm_sub_le _ _
    _ ≤ L / 2 * ‖T - x‖ ^ 2 + M / 2 * ‖T - x‖ ^ 2 := by
        have : ‖(M / 2 * ‖T - x‖) • (T - x)‖ = M / 2 * ‖T - x‖ ^ 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
        rw [this]
        linarith
    _ = 1 / 2 * (L + M) * ‖T - x‖ ^ 2 := by ring
