-- Prove2me | solution 1 for ConvexOptAlg.StrongGD.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:14:48.580985+00:00
-- url     : https://prove2.me/submissions/5488ebcf-d4f0-42d2-861a-dede0622bab2

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem sg311_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem sg311_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := sg311_line_deriv hF x w t
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
theorem sg311_gen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L : ℝ}
    (hfo : ∀ a b, F a + ⟪G a, b - a⟫ ≤ F b)
    (hd : ∀ a b, F b ≤ F a + ⟪G a, b - a⟫ + L / 2 * ‖b - a‖ ^ 2) (x y : E) (t : ℝ) :
    (2 * t - L * t ^ 2) * ‖G y - G x‖ ^ 2 ≤ ⟪G y - G x, y - x⟫ := by
  set v := G y - G x with hv
  have h1 := hfo x (y - t • v)
  have h2 := hd y (y - t • v)
  have h3 := hfo y (x + t • v)
  have h4 := hd x (x + t • v)
  have e1 : y - t • v - x = (y - x) - t • v := by abel
  have e2 : y - t • v - y = -(t • v) := by abel
  have e3 : x + t • v - y = -(y - x) + t • v := by abel
  have e4 : x + t • v - x = t • v := by abel
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4
  rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h2
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h4
  simp only [inner_sub_right, inner_add_right, inner_neg_right, inner_smul_right] at h1 h2 h3 h4
  have key : ⟪v, y - x⟫ = ⟪G y, y - x⟫ - ⟪G x, y - x⟫ := by rw [hv, inner_sub_left]
  have kv : ‖v‖ ^ 2 = ⟪G y, v⟫ - ⟪G x, v⟫ := by
    rw [← real_inner_self_eq_norm_sq, hv, inner_sub_left]
  have kt : 2 * t * ‖v‖ ^ 2 = 2 * t * (⟪G y, v⟫ - ⟪G x, v⟫) := by rw [kv]
  rw [key]
  simp only [inner_sub_right]
  linarith [h1, h2, h3, h4]

open scoped RealInnerProductSpace in
theorem sg311_main {n : ℕ} (f : ConvexOptAlg.StrongGD.E n → ℝ)
    (g : ConvexOptAlg.StrongGD.E n → ConvexOptAlg.StrongGD.E n) (α β : ℝ) (hα : 0 < α)
    (hsm : ConvexOptAlg.StrongGD.IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (x y : ConvexOptAlg.StrongGD.E n) :
    α * β / (β + α) * ‖x - y‖ ^ 2 + (1 / (β + α)) * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫ := by
  obtain ⟨hg, hβ, hlip⟩ := hsm
  set F : ConvexOptAlg.StrongGD.E n → ℝ := fun z => f z - α / 2 * ‖z‖ ^ 2 with hF
  set G : ConvexOptAlg.StrongGD.E n → ConvexOptAlg.StrongGD.E n := fun z => g z - α • z with hG
  have hfo : ∀ a b, F a + ⟪G a, b - a⟫ ≤ F b := by
    intro a b
    have h := hsc a (Set.mem_univ _) b (Set.mem_univ _)
    have e : ‖b - a‖ ^ 2 = ‖b‖ ^ 2 - 2 * ⟪a, b⟫ + ‖a‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm]
    simp only [hF, hG, inner_sub_left, inner_sub_right, inner_smul_left, real_inner_self_eq_norm_sq,
      RCLike.conj_to_real] at h ⊢
    rw [e] at h
    try rw [e]
    linarith [h]
  have hd : ∀ a b, F b ≤ F a + ⟪G a, b - a⟫ + (β - α) / 2 * ‖b - a‖ ^ 2 := by
    intro a b
    have h := sg311_descent hg hlip a b
    have e : ‖b - a‖ ^ 2 = ‖b‖ ^ 2 - 2 * ⟪a, b⟫ + ‖a‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm]
    simp only [hF, hG, inner_sub_left, inner_sub_right, inner_smul_left, real_inner_self_eq_norm_sq,
      RCLike.conj_to_real] at h ⊢
    rw [e] at h
    try rw [e]
    linarith [h]
  have hw : ‖G x - G y‖ ^ 2 ≤ (β - α) * ⟪G x - G y, x - y⟫ := by
    have ht : ∀ t : ℝ, (2 * t - (β - α) * t ^ 2) * ‖G x - G y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫ :=
      fun t => sg311_gen hfo hd y x t
    rcases lt_or_ge 0 (β - α) with hL | hL
    · have h1 := ht (1 / (β - α))
      have e : (2 * (1 / (β - α)) - (β - α) * (1 / (β - α)) ^ 2) = 1 / (β - α) := by
        field_simp; ring
      rw [e] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hL.le
      rw [← mul_assoc, mul_one_div_cancel hL.ne', one_mul] at h2
      exact h2
    · have hz : ‖G x - G y‖ ^ 2 = 0 := by
        by_contra hne
        have hpos : 0 < ‖G x - G y‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
        set c := ⟪G x - G y, x - y⟫
        set q := ‖G x - G y‖ ^ 2
        have h1 := ht ((|c| + 1) / (2 * q))
        have e : 2 * ((|c| + 1) / (2 * q)) * q = |c| + 1 := by field_simp
        have h3 : 0 ≤ -(β - α) * ((|c| + 1) / (2 * q)) ^ 2 * q := by
          apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hpos.le
        have h4 := le_abs_self c
        nlinarith
      have hz' : G x - G y = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
        exact norm_eq_zero.mp this
      rw [hz', inner_zero_left, mul_zero, norm_zero]; norm_num
  have eG : G x - G y = (g x - g y) - α • (x - y) := by
    simp only [hG, smul_sub]; abel
  rw [eG] at hw
  set u := g x - g y
  set d := x - y
  have e1 : ‖u - α • d‖ ^ 2 = ‖u‖ ^ 2 - 2 * (α * ⟪u, d⟫) + α ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have e2 : ⟪u - α • d, d⟫ = ⟪u, d⟫ - α * ‖d‖ ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [e1, e2] at hw
  have key : α * β * ‖d‖ ^ 2 + ‖u‖ ^ 2 ≤ (β + α) * ⟪u, d⟫ := by nlinarith [hw]
  have hpos : 0 < β + α := by linarith
  have : α * β / (β + α) * ‖d‖ ^ 2 + 1 / (β + α) * ‖u‖ ^ 2
      = (α * β * ‖d‖ ^ 2 + ‖u‖ ^ 2) / (β + α) := by field_simp
  rw [this, div_le_iff₀ hpos]
  linarith [key]

open scoped InnerProductSpace

open ConvexOptAlg.StrongGD InnerProductSpace in
theorem solution {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α) :
    ∀ x y : E n,
      α * β / (β + α) * ‖x - y‖ ^ 2 +
          (1 / (β + α)) * ‖g x - g y‖ ^ 2 ≤
        ⟪g x - g y, x - y⟫_ℝ := by
  intro x y
  exact sg311_main f g α β hα hsm hsc x y
