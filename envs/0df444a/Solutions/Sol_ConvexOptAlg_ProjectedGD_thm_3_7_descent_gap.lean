-- Prove2me | solution 1 for ConvexOptAlg.ProjectedGD.thm_3_7_descent_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:27:44.298753+00:00
-- url     : https://prove2.me/submissions/62a951ff-4f6a-429c-9c6c-15bc8d63c835

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

set_option autoImplicit false

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

theorem p88e_varineq {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcv : Convex ℝ X)
    (u p : EuclideanSpace ℝ (Fin n)) (hp : IsMetricProjection X u p) :
    ∀ w ∈ X, ⟪u - p, w - p⟫_ℝ ≤ 0 := by
  obtain ⟨hpX, hmin⟩ := hp
  refine (norm_eq_iInf_iff_real_inner_le_zero hXcv hpX).1 ?_
  have : Nonempty X := ⟨⟨p, hpX⟩⟩
  apply le_antisymm
  · refine le_ciInf ?_
    intro w
    have := hmin w w.2
    simpa [dist_eq_norm] using this
  · have hb : BddBelow (Set.range fun w : X => ‖u - (w : EuclideanSpace ℝ (Fin n))‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hb ⟨p, hpX⟩

theorem p88e_descent {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (a b : EuclideanSpace ℝ (Fin n)) (ha : a ∈ X) (hb : b ∈ X) :
    f b ≤ f a + inner ℝ (g a) (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set v := b - a with hv
  let p : ℝ → EuclideanSpace ℝ (Fin n) := fun s => a + s • v
  let G : ℝ → ℝ := fun s => f (p s) - f a - s * inner ℝ (g a) v - β / 2 * s ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ s : ℝ, HasDerivAt G
      (inner ℝ (g (p s)) v - inner ℝ (g a) v - β * s * ‖v‖ ^ 2) s := by
    intro s
    have hpd : HasDerivAt p v s := by
      have := ((hasDerivAt_id s).smul_const v).const_add a
      simpa [p] using this
    have hfg : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (g (p s))) (p s) :=
      hasGradientAt_iff_hasFDerivAt.mp (hgrad (p s))
    have h1 := hfg.comp_hasDerivAt s hpd
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g a) v) (inner ℝ (g a) v) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (g a) v)
    have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    have h1' : HasDerivAt (fun s => f (p s)) (inner ℝ (g (p s)) v) s := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h1
    exact ((h1'.sub_const (f a)).sub h2).sub h3
  have hnonpos : ∀ s ∈ Set.Icc (0:ℝ) 1,
      inner ℝ (g (p s)) v - inner ℝ (g a) v - β * s * ‖v‖ ^ 2 ≤ 0 := by
    intro s hs
    have hpsX : p s ∈ X := hXcv.add_smul_sub_mem ha hb hs
    have hle := hlip (p s) hpsX a ha
    have hps : p s - a = s • v := by simp [p]
    rw [hps, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at hle
    have hcs := real_inner_le_norm (g (p s) - g a) v
    rw [inner_sub_left] at hcs
    have : ‖g (p s) - g a‖ * ‖v‖ ≤ β * (s * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    nlinarith
  have hanti : AntitoneOn G (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s _; exact (hderiv s).continuousAt.continuousWithinAt
    · intro s _
      exact (hderiv s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hderiv s).deriv]
      exact hnonpos s (interior_subset hs)
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = b := by simp [p, v]
  simp only [G, hp0, hp1] at h01
  nlinarith

theorem p88e_convex_fo {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hXcv : Convex ℝ X)
    (hc : ConvexOn ℝ X f) (a b : EuclideanSpace ℝ (Fin n)) (ha : a ∈ X) (hb : b ∈ X) :
    f a + inner ℝ (g a) (b - a) ≤ f b := by
  set w := b - a
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (a + s • w)) (inner ℝ (g (a + t • w)) w) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => a + s • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add a
    have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hgrad (a + t • w))).comp_hasDerivAt t hl
    rw [InnerProductSpace.toDual_apply_apply] at h1
    exact h1
  have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t : ℝ => f (a + t • w)) := by
    have h0 := hc.comp_affineMap (AffineMap.lineMap a b)
    have e : (fun t : ℝ => f (a + t • w)) = f ∘ AffineMap.lineMap a b := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]
    refine h0.subset ?_ (convex_Icc 0 1)
    intro t ht
    simp only [Set.mem_preimage]
    have := hXcv.add_smul_sub_mem ha hb ht
    simpa [AffineMap.lineMap_apply, add_comm] using this
  have h := hφ.le_slope_of_hasDerivAt (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) zero_lt_one (by simpa using hline 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : a + w = b := by simp [w]
  rw [hw] at h
  linarith

/-- One projected step: `f(x⁺) - f(y) ≤ β/2 (‖x - y‖² - ‖x⁺ - y‖²)` for `x, y ∈ X`. -/
theorem p88e_step {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hc : ConvexOn ℝ X f)
    (x y p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hy : y ∈ X)
    (hp : IsMetricProjection X (x - β⁻¹ • g x) p) :
    f p - f y ≤ β / 2 * (‖x - y‖ ^ 2 - ‖p - y‖ ^ 2) := by
  have hpX : p ∈ X := hp.1
  have hv := p88e_varineq X hXcv _ _ hp y hy
  have hd := p88e_descent X hXcv f g β hgrad hlip x p hx hpX
  have hfo := p88e_convex_fo X f g hgrad hXcv hc x y hx hy
  have key : β • ((x - β⁻¹ • g x) - p) = β • (x - p) - g x := by
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul]
    abel
  have hv2 : ⟪β • (x - p) - g x, y - p⟫_ℝ ≤ 0 := by
    rw [← key, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos hβ.le hv
  have hpx : p - x = -(x - p) := (neg_sub x p).symm
  have hyx : y - x = -((x - p) + (p - y)) := by abel
  have hyp : y - p = -(p - y) := (neg_sub p y).symm
  have hxy : x - y = (x - p) + (p - y) := by abel
  rw [hpx, norm_neg, inner_neg_right] at hd
  rw [hyx, inner_neg_right, inner_add_right] at hfo
  rw [hyp, inner_neg_right, inner_sub_left, real_inner_smul_left] at hv2
  rw [hxy, norm_add_sq_real]
  linarith

open OnlineConvexOpt.FirstOrder in
open ConvexOptAlg.ProjectedGD in
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothOn X f g β)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsProjGDRun X g β x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (s : ℕ) (hs : 1 ≤ s) :
    f (x (s + 1)) - f (x s) ≤ -(1 / (2 * β)) * ‖gradMap β (x s) (x (s + 1))‖ ^ 2 ∧
      f (x (s + 1)) - f xstar ≤ ‖gradMap β (x s) (x (s + 1))‖ * ‖x s - xstar‖ := by
  obtain ⟨_, hgrad, hlip⟩ := hsmooth
  obtain ⟨_, hx1, hproj⟩ := hrun
  have hmem : ∀ k : ℕ, x (k + 1) ∈ X := by
    intro k
    cases k with
    | zero => exact hx1
    | succ k => exact (hproj (k + 1) (by omega)).1
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hstep : ∀ y ∈ X, f (x (k + 1 + 1)) - f y ≤
      β / 2 * (‖x (k + 1) - y‖ ^ 2 - ‖x (k + 1 + 1) - y‖ ^ 2) := by
    intro y hy
    exact p88e_step X hXcv f g β hβ hgrad hlip hf (x (k + 1)) y (x (k + 1 + 1)) (hmem k) hy
      (hproj (k + 1) (by omega))
  have hG : ‖gradMap β (x (k + 1)) (x (k + 1 + 1))‖ = β * ‖x (k + 1) - x (k + 1 + 1)‖ := by
    rw [gradMap, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  rw [hG]
  set a := x (k + 1) - x (k + 1 + 1) with ha
  set u := x (k + 1) - xstar with hu
  have h1 := hstep xstar hxstar
  have h2 := hstep (x (k + 1)) (hmem k)
  have hua : x (k + 1 + 1) - xstar = u - a := by simp [ha, hu]
  have hna : ‖x (k + 1 + 1) - x (k + 1)‖ = ‖a‖ := by rw [ha, norm_sub_rev]
  rw [hua, norm_sub_sq_real u a] at h1
  rw [sub_self, norm_zero, hna] at h2
  have hcs : ⟪u, a⟫_ℝ ≤ ‖u‖ * ‖a‖ := real_inner_le_norm u a
  constructor
  · have e : -(1 / (2 * β)) * (β * ‖a‖) ^ 2 = β / 2 * (0 ^ 2 - ‖a‖ ^ 2) := by
      field_simp
      ring
    rw [e]
    exact h2
  · have : f (x (k + 1 + 1)) - f xstar ≤ β * ⟪u, a⟫_ℝ - β / 2 * ‖a‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖a‖, mul_le_mul_of_nonneg_left hcs hβ.le]
