-- Prove2me | solution 1 for CubicNewton.Nonconvex.grad_norm_at_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:59:44.639144+00:00
-- url     : https://prove2.me/submissions/1658066f-f28c-4ee9-82e3-6a93847217c5

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Symmetry of the Hessian on a convex set with nonempty interior. -/
theorem aux_gns_symm {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hF_convex : Convex ℝ F) (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪H x v, w⟫ = ⟪H x w, v⟫ := by
  have h1 : ∀ y ∈ interior F, HasFDerivAt f (innerSL ℝ (g y)) y := by
    intro y hy
    exact (hf y (interior_subset hy))
  have h2 : HasFDerivWithinAt (fun y => innerSL ℝ (g y)) ((innerSL ℝ).comp (H x))
      (interior F) x :=
    ((innerSL ℝ).hasFDerivAt.comp x (hg x hx)).hasFDerivWithinAt
  have := hF_convex.second_derivative_within_at_symmetric hF_int h1 hx h2 v w
  simpa using this

/-- First-order optimality condition for a global minimizer of the cubic model. -/
theorem aux_gns_foc {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T)
    (hsymm : ∀ v w, ⟪H x v, w⟫ = ⟪H x w, v⟫) :
    g x + H x (T - x) + (M / 2 * ‖T - x‖) • (T - x) = 0 := by
  set h := T - x with hh
  set d := g x + H x h + (M / 2 * ‖h‖) • h with hd
  let φ : ℝ → ℝ := fun t => CubicNewton.Shared.cubicModel g H M x (T + t • d)
  have hmin : IsLocalMin φ 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [φ, zero_smul, add_zero]
    exact hT _
  have hu : HasDerivAt (fun t : ℝ => T + t • d - x) d 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add T).sub_const x
  have hu0 : T + (0 : ℝ) • d - x = h := by simp [hh]
  have t1 := (hasDerivAt_const (0 : ℝ) (g x)).inner ℝ hu
  have t2 := ((H x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu).inner ℝ hu
  have t3 := (hasFDerivAt_norm_rpow (T + (0 : ℝ) • d - x) (p := 3) (by norm_num)).comp_hasDerivAt
    (0 : ℝ) hu
  have t3' : HasDerivAt (fun t : ℝ => ‖T + t • d - x‖ ^ 3)
      (3 * ‖h‖ * ⟪h, d⟫) 0 := by
    have e : (fun t : ℝ => ‖T + t • d - x‖ ^ 3) =
        ((fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (3 : ℝ)) ∘ fun t : ℝ => T + t • d - x) := by
      ext t
      simp only [Function.comp]
      exact (Real.rpow_ofNat _ 3).symm
    rw [e]
    refine t3.congr_deriv ?_
    rw [hu0]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
    norm_num
  have hall := (t1.add (t2.const_mul (1 / 2 : ℝ))).add (t3'.const_mul (M / 6))
  have hderiv : HasDerivAt φ (⟪d, d⟫) 0 := by
    refine hall.congr_deriv ?_
    simp only [Function.comp, hu0, inner_zero_left, add_zero]
    rw [hsymm d h]
    have e2 : ⟪d, d⟫ = ⟪g x + H x h + (M / 2 * ‖h‖) • h, d⟫ := by rw [← hd]
    rw [e2, inner_add_left, inner_add_left, real_inner_smul_left]
    ring
  have := hmin.hasDerivAt_eq_zero hderiv
  exact inner_self_eq_zero.mp this

/-- Taylor-type bound for the gradient along a segment in `F`. -/
theorem aux_gns_taylor {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ) (hF_convex : Convex ℝ F)
    (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F) :
    ‖g T - g x - H x (T - x)‖ ≤ L / 2 * ‖T - x‖ ^ 2 := by
  set h := T - x with hh
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ F := fun t ht =>
    hF_convex.add_smul_sub_mem hx hTF ht
  let φ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => g (x + t • h) - g x - t • H x h
  let φ' : ℝ → EuclideanSpace ℝ (Fin n) := fun t => H (x + t • h) h - H x h
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 := (hg _ (hseg t ht)).comp_hasDerivAt t h1
    have h3 := (h2.sub_const (g x)).sub ((hasDerivAt_id t).smul_const (H x h))
    have h4 := h3.congr_deriv (show (H (x + t • h)) h - (1:ℝ) • (H x) h = φ' t by simp [φ'])
    exact h4
  have hcont : ContinuousOn φ (Set.Icc 0 1) := fun t ht =>
    (hφ t ht).continuousAt.continuousWithinAt
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖h‖ ^ 2) (L * t * ‖h‖ ^ 2) t := by
    intro t
    have := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖h‖ ^ 2)
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖φ' t‖ ≤ L * t * ‖h‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    have hLt := hLip (x + t • h) (hseg t ht') x hx
    have e1 : x + t • h - x = t • h := by abel
    rw [e1, norm_smul, Real.norm_of_nonneg ht.1] at hLt
    calc ‖φ' t‖ = ‖(H (x + t • h) - H x) h‖ := by simp [φ']
      _ ≤ ‖H (x + t • h) - H x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * (t * ‖h‖) * ‖h‖ := by gcongr
      _ = L * t * ‖h‖ ^ 2 := by ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ) (f' := φ')
    (a := 0) (b := 1) hcont
    (fun t ht => (hφ t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun t : ℝ => L / 2 * t ^ 2 * ‖h‖ ^ 2) (B' := fun t : ℝ => L * t * ‖h‖ ^ 2)
    (by simp [φ]) hB hbound (Set.right_mem_Icc.2 zero_le_one)
  simpa [φ, hh] using key

end CubicNewton.Nonconvex

open CubicNewton.Nonconvex

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
  have hsymm := aux_gns_symm F f g H hF_convex hF_int hf hg x hx
  have hfoc := aux_gns_foc g H M x T hT hsymm
  have htay := aux_gns_taylor F g H L hF_convex hg hL hLip x T hx hTF
  have e : g T = (g T - g x - H x (T - x)) - (M / 2 * ‖T - x‖) • (T - x) := by
    rw [show (g T - g x - H x (T - x)) - (M / 2 * ‖T - x‖) • (T - x) =
      g T - (g x + H x (T - x) + (M / 2 * ‖T - x‖) • (T - x)) by abel, hfoc, sub_zero]
  rw [e, norm_sub_rev x T]
  calc ‖(g T - g x - H x (T - x)) - (M / 2 * ‖T - x‖) • (T - x)‖
      ≤ ‖g T - g x - H x (T - x)‖ + ‖(M / 2 * ‖T - x‖) • (T - x)‖ := norm_sub_le _ _
    _ ≤ L / 2 * ‖T - x‖ ^ 2 + M / 2 * ‖T - x‖ ^ 2 := by
        gcongr
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact le_of_eq (by ring)
    _ = 1 / 2 * (L + M) * ‖T - x‖ ^ 2 := by ring
