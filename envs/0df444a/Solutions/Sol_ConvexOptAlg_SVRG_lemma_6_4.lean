-- Prove2me | solution 1 for ConvexOptAlg.SVRG.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:39:46.365282+00:00
-- url     : https://prove2.me/submissions/c7dcf7bb-8a40-45af-a9f6-d231258f50f8

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem svrg64_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem svrg64_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := svrg64_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

open scoped RealInnerProductSpace in
theorem svrg64_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => F (x + t • w)) := by
    have := hc.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => F (x + t • w)) = F ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using svrg64_line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

-- Co-coercivity: ‖G y - G x‖² ≤ 2L (F y - F x - ⟪G x, y - x⟫).
open scoped RealInnerProductSpace in
theorem svrg64_cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (hc : ConvexOn ℝ Set.univ F) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * L * (F y - F x - ⟪G x, y - x⟫) := by
  -- φ z = F z - ⟪G x, z⟫, gradient H z = G z - G x
  set φ : E → ℝ := fun z => F z - ⟪G x, z⟫ with hφdef
  set H : E → E := fun z => G z - G x with hHdef
  have hφ : ∀ z, HasGradientAt φ (H z) z := by
    intro z
    have h1 := hasGradientAt_iff_hasFDerivAt.mp (hF z)
    have h2 : HasFDerivAt (fun z : E => ⟪G x, z⟫) (InnerProductSpace.toDual ℝ E (G x)) z := by
      have e : (fun z : E => ⟪G x, z⟫) = ⇑(InnerProductSpace.toDual ℝ E (G x)) := by
        funext z; simp [InnerProductSpace.toDual_apply_apply]
      rw [e]; exact ContinuousLinearMap.hasFDerivAt _
    rw [hasGradientAt_iff_hasFDerivAt, map_sub]
    exact h1.sub h2
  have hH : ∀ a b, ‖H a - H b‖ ≤ L * ‖a - b‖ := by
    intro a b; simp only [hHdef, sub_sub_sub_cancel_right]; exact hG a b
  -- φ minimized at x
  have hmin : ∀ z, φ x ≤ φ z := by
    intro z
    have := svrg64_convex_fo hF hc x z
    simp only [hφdef, inner_sub_right] at this ⊢
    linarith
  set v := H y
  have hd := svrg64_descent hφ hH y (y - (1 / L) • v)
  have hm := hmin (y - (1 / L) • v)
  have e1 : y - (1 / L) • v - y = -((1 / L) • v) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / L), real_inner_self_eq_norm_sq] at hd
  have key : ‖v‖ ^ 2 ≤ 2 * L * (φ y - φ x) := by
    have hL' : L ≠ 0 := hL.ne'
    have : φ x ≤ φ y - 1 / (2 * L) * ‖v‖ ^ 2 := by
      have h := hm.trans hd
      have : -(1 / L * ‖v‖ ^ 2) + L / 2 * (1 / L * ‖v‖) ^ 2 = - (1 / (2 * L) * ‖v‖ ^ 2) := by
        field_simp; ring
      linarith
    have h2 : 2 * L * (1 / (2 * L) * ‖v‖ ^ 2) = ‖v‖ ^ 2 := by field_simp
    nlinarith
  have hv : v = G y - G x := rfl
  rw [← hv]
  have : φ y - φ x = F y - F x - ⟪G x, y - x⟫ := by
    simp only [hφdef, inner_sub_right]; ring
  rw [← this]; exact key

open scoped RealInnerProductSpace in
theorem svrg64_grad_sum_zero {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ i x, HasGradientAt (fs i) (gs i x) x) (xstar w : EuclideanSpace ℝ (Fin n))
    (hmin : ∀ z, ∑ i, fs i xstar ≤ ∑ i, fs i z) :
    ∑ i, ⟪gs i xstar, w⟫ = 0 := by
  have hd : HasFDerivAt (fun z => ∑ i, fs i z)
      (∑ i, InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gs i xstar)) xstar :=
    HasFDerivAt.fun_sum (fun i _ => hasGradientAt_iff_hasFDerivAt.mp (hg i xstar))
  have hlm : IsLocalMin (fun z => ∑ i, fs i z) xstar :=
    Filter.Eventually.of_forall (fun z => hmin z)
  have h0 := hlm.hasFDerivAt_eq_zero hd
  have := congrArg (fun L => L w) h0
  simpa [ContinuousLinearMap.sum_apply, InnerProductSpace.toDual_apply_apply] using this

open ConvexOptAlg.SVRG RealInnerProductSpace in
theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) (x xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ‖gs i x - gs i xstar‖ ^ 2) ≤
      2 * β * (objective fs x - objective fs xstar) := by
  obtain ⟨hg, hc, hL⟩ := hfamily
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hmin' : ∀ z, ∑ i, fs i xstar ≤ ∑ i, fs i z := by
    intro z
    have := hmin z
    simp only [objective, uniformMean, Fintype.card_fin] at this
    exact (div_le_div_iff_of_pos_right hmR).mp this
  have h0 := svrg64_grad_sum_zero fs gs hg xstar (x - xstar) hmin'
  have hi : ∀ i, ‖gs i x - gs i xstar‖ ^ 2 ≤
      2 * β * (fs i x - fs i xstar - ⟪gs i xstar, x - xstar⟫) := fun i =>
    svrg64_cocoercive hβ (hg i) (hL i) (hc i) xstar x
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h0] at hs
  simp only [objective, uniformMean, Fintype.card_fin]
  rw [div_le_iff₀ hmR]
  have e : 2 * β * ((∑ i, fs i x) / (m:ℝ) - (∑ i, fs i xstar) / (m:ℝ)) * (m:ℝ)
      = 2 * β * (∑ i, fs i x - ∑ i, fs i xstar) := by
    field_simp
  rw [e]; linarith
