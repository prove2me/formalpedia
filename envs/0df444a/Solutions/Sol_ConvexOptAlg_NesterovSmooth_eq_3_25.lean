-- Prove2me | solution 1 for ConvexOptAlg.NesterovSmooth.eq_3_25
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:47:54.62775+00:00
-- url     : https://prove2.me/submissions/e32f5720-86c0-42cb-af45-3c822e8cef63

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs

set_option autoImplicit false

open scoped InnerProductSpace

theorem ns725_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (a b : EuclideanSpace ℝ (Fin n)) :
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
    have hle := hlip (p s) a
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

theorem ns725_convex_fo {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
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

theorem ns725_lam_ge_one (s : ℕ) (hs : 1 ≤ s) : 1 ≤ ConvexOptAlg.NesterovSmooth.lam s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [ConvexOptAlg.NesterovSmooth.lam]
  have h := Real.sqrt_le_sqrt
    (show (1:ℝ) ≤ 1 + 4 * ConvexOptAlg.NesterovSmooth.lam t ^ 2 by
      nlinarith [sq_nonneg (ConvexOptAlg.NesterovSmooth.lam t)])
  rw [Real.sqrt_one] at h
  linarith

theorem ns725_lam_sq (s : ℕ) (hs : 1 ≤ s) :
    ConvexOptAlg.NesterovSmooth.lam (s - 1) ^ 2 =
      ConvexOptAlg.NesterovSmooth.lam s ^ 2 - ConvexOptAlg.NesterovSmooth.lam s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [ConvexOptAlg.NesterovSmooth.lam]
  have h0 : (0:ℝ) ≤ 1 + 4 * ConvexOptAlg.NesterovSmooth.lam t ^ 2 := by positivity
  have hr := Real.sq_sqrt h0
  nlinarith [hr]

open ConvexOptAlg.NesterovSmooth in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (s : ℕ) (hs : 1 ≤ s) :
    lam s ^ 2 * (f (y (s + 1)) - f xstar) - lam (s - 1) ^ 2 * (f (y s) - f xstar) ≤
      β / 2 * (‖lam s • x s - (lam s - 1) • y s - xstar‖ ^ 2 -
        ‖lam s • y (s + 1) - (lam s - 1) • y s - xstar‖ ^ 2) := by
  obtain ⟨hgrad, hlip⟩ := hf
  have hy := (hrun.2 s hs).1
  have hL1 := ns725_lam_ge_one s hs
  rw [ns725_lam_sq s hs]
  set L := lam s with hL
  set G := g (x s) with hG
  have hd := ns725_descent f g β hgrad hlip (x s) (y (s + 1))
  have hc1 := ns725_convex_fo Set.univ f g hgrad convex_univ hconv (x s) (y s)
    (Set.mem_univ _) (Set.mem_univ _)
  have hc2 := ns725_convex_fo Set.univ f g hgrad convex_univ hconv (x s) xstar
    (Set.mem_univ _) (Set.mem_univ _)
  have e1 : y (s + 1) - x s = -((1 / β) • G) := by rw [hy]; abel
  rw [e1, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / β)] at hd
  have e3 : inner ℝ G (y s - x s) = -inner ℝ G (x s - y s) := by
    rw [← inner_neg_right, neg_sub]
  have e4 : inner ℝ G (xstar - x s) = -inner ℝ G (x s - xstar) := by
    rw [← inner_neg_right, neg_sub]
  rw [e3] at hc1
  rw [e4] at hc2
  set W := L • x s - (L - 1) • y s - xstar with hW
  have ew : L • y (s + 1) - (L - 1) • y s - xstar = W - (L / β) • G := by
    rw [hW, hy]; module
  have ewd : W = (L - 1) • (x s - y s) + (x s - xstar) := by rw [hW]; module
  have hWG : inner ℝ W G = (L - 1) * inner ℝ G (x s - y s) + inner ℝ G (x s - xstar) := by
    rw [ewd, inner_add_left, real_inner_smul_left, real_inner_comm, real_inner_comm G (x s - xstar)]
  rw [← hG] at hd
  rw [ew, norm_sub_sq_real (x := W), inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ L / β), hWG]
  have hLL : 0 ≤ L ^ 2 - L := by nlinarith
  have k1 : (L ^ 2 - L) * (f (x s) - inner ℝ G (x s - y s)) ≤ (L ^ 2 - L) * f (y s) :=
    mul_le_mul_of_nonneg_left (by linarith) hLL
  have k2 : L * (f (x s) - inner ℝ G (x s - xstar)) ≤ L * f xstar :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have k3 : L ^ 2 * f (y (s + 1)) ≤ L ^ 2 * (f (x s) + -(1 / β * ‖G‖ ^ 2) +
      β / 2 * (1 / β * ‖G‖) ^ 2) := mul_le_mul_of_nonneg_left hd (by positivity)
  have hβ' : β ≠ 0 := hβ.ne'
  have hR : ∀ (A N : ℝ), β / 2 * (2 * (L / β * A) - (L / β * N) ^ 2) =
      L * A - L ^ 2 * (1 / β) * N ^ 2 / 2 := by
    intro A N; field_simp
  have hR2 : L ^ 2 * (β / 2 * (1 / β * ‖G‖) ^ 2) = L ^ 2 * (1 / β) * ‖G‖ ^ 2 / 2 := by
    field_simp
  have hR' := hR ((L - 1) * inner ℝ G (x s - y s) + inner ℝ G (x s - xstar)) ‖G‖
  nlinarith [hR', hR2, k1, k2, k3]
