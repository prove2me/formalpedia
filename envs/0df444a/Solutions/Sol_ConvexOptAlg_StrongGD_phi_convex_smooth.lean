-- Prove2me | solution 1 for ConvexOptAlg.StrongGD.phi_convex_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:34:57.807229+00:00
-- url     : https://prove2.me/submissions/9e9ce02e-879e-427e-a8be-a83d758476c0

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

set_option autoImplicit false

open scoped InnerProductSpace

open scoped RealInnerProductSpace in
theorem p4d0_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem p4d0_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := p4d0_line_deriv hF x w t
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

-- First-order lower bound gives convexity.
open scoped RealInnerProductSpace in
theorem p4d0_convex_of_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} (hLo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) :
    ConvexOn ℝ (Set.univ : Set E) F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h1 := hLo (a • x + b • y) x
  have h2 := hLo (a • x + b • y) y
  have e : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))
        = (a • x + b • y) - (a + b) • (a • x + b • y) := by
      simp only [smul_sub, add_smul]; abel
    rw [this, hab, one_smul, sub_self]
  have e2 : a * ⟪G (a • x + b • y), x - (a • x + b • y)⟫
      + b * ⟪G (a • x + b • y), y - (a • x + b • y)⟫ = 0 := by
    have := congrArg (fun v => ⟪G (a • x + b • y), v⟫) e
    simpa [inner_add_right, real_inner_smul_right] using this
  simp only [smul_eq_mul]
  have k1 := mul_le_mul_of_nonneg_left h1 ha
  have k2 := mul_le_mul_of_nonneg_left h2 hb
  rw [mul_add] at k1 k2
  have hz : F (a • x + b • y) = a * F (a • x + b • y) + b * F (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  linarith

-- Convex lower bound + quadratic upper bound give an `L`-Lipschitz gradient.
open scoped RealInnerProductSpace in
theorem p4d0_lip_of_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hLo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y)
    (hU : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) (x y : E) :
    ‖G x - G y‖ ≤ L * ‖x - y‖ := by
  set w := G y - G x with hw
  set d := y - x with hd
  have ew : ‖w‖ ^ 2 = ⟪G y, w⟫ - ⟪G x, w⟫ := by
    rw [← real_inner_self_eq_norm_sq, hw, inner_sub_left]
  have ed : ⟪w, d⟫ = ⟪G y, d⟫ - ⟪G x, d⟫ := by rw [hw, inner_sub_left]
  have key : ∀ t : ℝ, (2 * t - L * t ^ 2) * ‖w‖ ^ 2 ≤ ⟪w, d⟫ := by
    intro t
    have nt : ‖t • w‖ ^ 2 = t ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have A1 : F x + (⟪G x, d⟫ - t * ⟪G x, w⟫) ≤ F (y - t • w) := by
      have := hLo x (y - t • w)
      rwa [show y - t • w - x = d - t • w by rw [hd]; abel, inner_sub_right,
        real_inner_smul_right] at this
    have A2 : F (y - t • w) ≤ F y + (-(t * ⟪G y, w⟫)) + L / 2 * (t ^ 2 * ‖w‖ ^ 2) := by
      have := hU y (y - t • w)
      rwa [show y - t • w - y = -(t • w) by abel, inner_neg_right, real_inner_smul_right,
        norm_neg, nt] at this
    have B1 : F y + (-⟪G y, d⟫ + t * ⟪G y, w⟫) ≤ F (x + t • w) := by
      have := hLo y (x + t • w)
      rwa [show x + t • w - y = -d + t • w by rw [hd]; abel, inner_add_right, inner_neg_right,
        real_inner_smul_right] at this
    have B2 : F (x + t • w) ≤ F x + t * ⟪G x, w⟫ + L / 2 * (t ^ 2 * ‖w‖ ^ 2) := by
      have := hU x (x + t • w)
      rwa [show x + t • w - x = t • w by abel, real_inner_smul_right, nt] at this
    have ew' : t * ‖w‖ ^ 2 = t * ⟪G y, w⟫ - t * ⟪G x, w⟫ := by rw [ew]; ring
    linarith
  have cs : ⟪w, d⟫ ≤ ‖w‖ * ‖d‖ := real_inner_le_norm w d
  have hn1 : ‖G x - G y‖ = ‖w‖ := by rw [hw, norm_sub_rev]
  have hn2 : ‖x - y‖ = ‖d‖ := by rw [hd, norm_sub_rev]
  rw [hn1, hn2]
  rcases hL.lt_or_eq with hLp | hL0
  · have k := key (1 / L)
    have e : (2 * (1 / L) - L * (1 / L) ^ 2) = 1 / L := by field_simp; ring
    rw [e] at k
    have k2 : ‖w‖ ^ 2 ≤ L * (‖w‖ * ‖d‖) := by
      have := mul_le_mul_of_nonneg_left (k.trans cs) hLp.le
      rwa [← mul_assoc, mul_one_div_cancel hLp.ne', one_mul] at this
    by_contra hcon
    push Not at hcon
    have hwpos : 0 < ‖w‖ := lt_of_le_of_lt (by positivity) hcon
    nlinarith
  · subst hL0
    by_contra hcon
    push Not at hcon
    have hwpos : 0 < ‖w‖ := lt_of_le_of_lt (by simp) hcon
    have k := key ((‖d‖ + 1) / ‖w‖)
    have e : (2 * ((‖d‖ + 1) / ‖w‖) - 0 * ((‖d‖ + 1) / ‖w‖) ^ 2) * ‖w‖ ^ 2
        = 2 * (‖d‖ + 1) * ‖w‖ := by field_simp; ring
    rw [e] at k
    nlinarith [norm_nonneg d]

open ConvexOptAlg.StrongGD in
open scoped RealInnerProductSpace in
theorem p4d0_phi_grad {n : ℕ} (f : E n → ℝ) (g : E n → E n) (α : ℝ)
    (hF : ∀ x, HasGradientAt f (g x) x) (z : E n) :
    HasGradientAt (phi f α) (g z - α • z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := hasGradientAt_iff_hasFDerivAt.mp (hF z)
  have h2 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (α / 2)
  have h3 := h1.sub h2
  refine h3.congr_fderiv ?_
  ext v
  simp [InnerProductSpace.toDual_apply_apply]
  ring

open ConvexOptAlg.StrongGD in
open scoped RealInnerProductSpace in
theorem p4d0_phi_lower {n : ℕ} (f : E n → ℝ) (g : E n → E n) (α : ℝ)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α) (x y : E n) :
    phi f α x + ⟪g x - α • x, y - x⟫ ≤ phi f α y := by
  have h := hsc x (Set.mem_univ _) y (Set.mem_univ _)
  have e1 : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have e2 : ⟪g x - α • x, y - x⟫ = ⟪g x, y - x⟫ - α * (⟪x, y⟫ - ‖x‖ ^ 2) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have e3 : ⟪x, y⟫ = ⟪y, x⟫ := real_inner_comm _ _
  simp only [phi]
  rw [e2, e3]
  rw [e1] at h
  linarith

open ConvexOptAlg.StrongGD in
open scoped RealInnerProductSpace in
theorem p4d0_phi_upper {n : ℕ} (f : E n → ℝ) (g : E n → E n) (α β : ℝ)
    (hsm : IsBetaSmooth f g β) (x y : E n) :
    phi f α y ≤ phi f α x + ⟪g x - α • x, y - x⟫ + (β - α) / 2 * ‖y - x‖ ^ 2 := by
  obtain ⟨hF, -, hG⟩ := hsm
  have h := p4d0_descent hF hG x y
  have e1 : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have e2 : ⟪g x - α • x, y - x⟫ = ⟪g x, y - x⟫ - α * (⟪x, y⟫ - ‖x‖ ^ 2) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have e3 : ⟪x, y⟫ = ⟪y, x⟫ := real_inner_comm _ _
  simp only [phi]
  rw [e2, e3, e1]
  rw [e1] at h
  linarith

open ConvexOptAlg.StrongGD in
theorem solution {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α) :
    ConvexOn ℝ (Set.univ : Set (E n)) (phi f α) ∧
      IsBetaSmooth (phi f α) (fun z => g z - α • z) (β - α) := by
  have hLo := p4d0_phi_lower f g α hsc
  have hU := p4d0_phi_upper f g α β hsm
  -- 0 ≤ β - α from a unit vector
  set w : E n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) with hwdef
  have hw1 : ‖w‖ = 1 := by rw [hwdef, PiLp.norm_single]; simp
  have hL : 0 ≤ β - α := by
    have a := hLo 0 w
    have b := hU 0 w
    simp only [sub_zero, smul_zero] at a b
    rw [hw1] at b
    linarith
  refine ⟨p4d0_convex_of_lower (G := fun z => g z - α • z) hLo, ?_, hL, ?_⟩
  · exact p4d0_phi_grad f g α hsm.1
  · exact p4d0_lip_of_bounds (G := fun z => g z - α • z) hL hLo hU
