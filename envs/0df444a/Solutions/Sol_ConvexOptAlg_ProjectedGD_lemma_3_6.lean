-- Prove2me | solution 1 for ConvexOptAlg.ProjectedGD.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:03:41.724168+00:00
-- url     : https://prove2.me/submissions/687cd6aa-7618-4ec6-a9a1-fc062a0c1fa4

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

set_option autoImplicit false

open scoped InnerProductSpace

/-- Gradient inequality for a convex function differentiable at `x`. -/
theorem pgd36_grad_ineq {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ X f)
    (x y gx : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hy : y ∈ X)
    (hg : HasGradientAt f gx x) :
    f x + ⟪gx, y - x⟫_ℝ ≤ f y := by
  set d := y - x with hd
  have hγ : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have hF : HasFDerivAt f (InnerProductSpace.toDual ℝ _ gx) (x + (0:ℝ) • d) := by
    simpa using hasGradientAt_iff_hasFDerivAt.mp hg
  have hφ : HasDerivAt (fun t : ℝ => f (x + t • d)) ⟪gx, d⟫_ℝ 0 := by
    have := hF.comp_hasDerivAt (0:ℝ) hγ
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this
  have ht := (hasDerivAt_iff_tendsto_slope.mp hφ).mono_left
    (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
  suffices hs : ⟪gx, d⟫_ℝ ≤ f y - f x by linarith
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hc := hf.2 hx hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
  have he : (1 - t) • x + t • y = x + t • d := by
    rw [hd, smul_sub, sub_smul, one_smul]; abel
  rw [he, smul_eq_mul, smul_eq_mul] at hc
  rw [slope_def_field]
  simp only [zero_smul, add_zero, sub_zero]
  rw [div_le_iff₀ ht0]
  linarith

/-- Descent lemma from a `β`-Lipschitz gradient on a convex set. -/
theorem pgd36_descent {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hp : p ∈ X) :
    f p ≤ f x + ⟪g x, p - x⟫_ℝ + β / 2 * ‖p - x‖ ^ 2 := by
  set d := p - x with hd
  let φ : ℝ → ℝ := fun t => f (x + t • d) - t * ⟪g x, d⟫_ℝ - β / 2 * t ^ 2 * ‖d‖ ^ 2
  have hder : ∀ t : ℝ, HasDerivAt φ
      (⟪g (x + t • d), d⟫_ℝ - ⟪g x, d⟫_ℝ - β * t * ‖d‖ ^ 2) t := by
    intro t
    have hγ : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hF := hasGradientAt_iff_hasFDerivAt.mp (hgrad (x + t • d))
    have h1 : HasDerivAt (fun s : ℝ => f (x + s • d)) ⟪g (x + t • d), d⟫_ℝ t := by
      have := hF.comp_hasDerivAt t hγ
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪g x, d⟫_ℝ) ⟪g x, d⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪g x, d⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖d‖ ^ 2) (β * t * ‖d‖ ^ 2) t := by
      have h := (hasDerivAt_pow 2 t).const_mul (β / 2 * ‖d‖ ^ 2)
      have hfun : (fun s : ℝ => β / 2 * s ^ 2 * ‖d‖ ^ 2)
          = fun s : ℝ => β / 2 * ‖d‖ ^ 2 * s ^ 2 := by
        funext s; ring
      rw [hfun]
      refine h.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hder t).continuousAt.continuousWithinAt
    · exact fun t _ => (hder t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have hmem : x + t • d ∈ X := by
        have := hXcv.add_smul_sub_mem hx hp ⟨ht0.le, ht1.le⟩
        simpa [hd] using this
      have hL := hlip (x + t • d) hmem x hx
      have hn : ‖x + t • d - x‖ = t * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      rw [hn] at hL
      have hcs : ⟪g (x + t • d) - g x, d⟫_ℝ ≤ ‖g (x + t • d) - g x‖ * ‖d‖ :=
        real_inner_le_norm _ _
      rw [inner_sub_left] at hcs
      have : ‖g (x + t • d) - g x‖ * ‖d‖ ≤ β * (t * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  have hd' : x + (1:ℝ) • d = p := by rw [one_smul, hd]; abel
  simp only [φ, hd', zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  linarith

/-- Variational inequality for a metric projection onto a convex set. -/
theorem pgd36_proj_vi {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcv : Convex ℝ X)
    (u p : EuclideanSpace ℝ (Fin n))
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection X u p) :
    ∀ w ∈ X, ⟪u - p, w - p⟫_ℝ ≤ 0 := by
  obtain ⟨hpX, hmin⟩ := hp
  have hne : Nonempty X := ⟨⟨p, hpX⟩⟩
  have hbdd : BddBelow (Set.range fun w : X => ‖u - (w : EuclideanSpace ℝ (Fin n))‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  have hle1 : ‖u - p‖ ≤ ⨅ w : X, ‖u - (w : EuclideanSpace ℝ (Fin n))‖ := by
    apply le_ciInf
    intro w
    have := hmin w w.2
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hle2 : ⨅ w : X, ‖u - (w : EuclideanSpace ℝ (Fin n))‖ ≤ ‖u - p‖ :=
    ciInf_le hbdd ⟨p, hpX⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hXcv hpX).mp (le_antisymm hle1 hle2)

open InnerProductSpace OnlineConvexOpt.FirstOrder ConvexOptAlg.ProjectedGD in
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothOn X f g β)
    (x y xplus : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hy : y ∈ X)
    (hplus : IsMetricProjection X (x - β⁻¹ • g x) xplus) :
    f xplus - f y ≤ ⟪gradMap β x xplus, x - y⟫_ℝ - 1 / (2 * β) * ‖gradMap β x xplus‖ ^ 2 := by
  obtain ⟨-, hgrad, hlip⟩ := hsmooth
  have hpX : xplus ∈ X := hplus.1
  have hA := pgd36_descent X hXcv f g β hgrad hlip x xplus hx hpX
  have hB := pgd36_grad_ineq X f hf x y (g x) hx hy (hgrad x)
  have hC := pgd36_proj_vi X hXcv _ _ hplus y hy
  set a := x - xplus with ha
  set b := y - xplus with hb
  have e1 : xplus - x = -a := by rw [ha]; abel
  have e2 : y - x = b - a := by rw [ha, hb]; abel
  have e3 : x - y = a - b := by rw [ha, hb]; abel
  have e4 : x - β⁻¹ • g x - xplus = a - β⁻¹ • g x := by rw [ha]; abel
  rw [e1, inner_neg_right, norm_neg] at hA
  rw [e2, inner_sub_right] at hB
  rw [e4, inner_sub_left, inner_smul_left] at hC
  simp only [conj_trivial] at hC
  unfold gradMap
  rw [← ha, e3, inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_of_pos hβ]
  simp only [conj_trivial]
  have hC' : β * ⟪a, b⟫_ℝ ≤ ⟪g x, b⟫_ℝ := by
    have h := mul_le_mul_of_nonneg_left hC hβ.le
    rw [mul_zero, mul_sub, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul] at h
    linarith
  have hq : 1 / (2 * β) * (β * ‖a‖) ^ 2 = β / 2 * ‖a‖ ^ 2 := by
    field_simp
  rw [hq]
  nlinarith [hA, hB, hC']
