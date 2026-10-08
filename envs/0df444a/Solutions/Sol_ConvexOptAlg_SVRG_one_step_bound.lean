-- Prove2me | solution 1 for ConvexOptAlg.SVRG.one_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:50:08.222004+00:00
-- url     : https://prove2.me/submissions/a44a4651-5c8c-4a17-b395-def728cb2b5d

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem svrg61_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem svrg61_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := svrg61_line_deriv hF x w t
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
theorem svrg61_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (by simpa using svrg61_line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

-- Co-coercivity: ‖G y - G x‖² ≤ 2L (F y - F x - ⟪G x, y - x⟫).
open scoped RealInnerProductSpace in
theorem svrg61_cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    have := svrg61_convex_fo hF hc x z
    simp only [hφdef, inner_sub_right] at this ⊢
    linarith
  set v := H y
  have hd := svrg61_descent hφ hH y (y - (1 / L) • v)
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

namespace SVRG61Help

open ConvexOptAlg.SVRG
open scoped RealInnerProductSpace

theorem obj_sum {n m : ℕ} (hm : 0 < m) (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, fs i x = (m:ℝ) * objective fs x := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold objective uniformMean
  rw [Fintype.card_fin]; field_simp

theorem grad_sum {n m : ℕ} (hm : 0 < m)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : (m:ℝ) • fullGradient gs x = ∑ i, gs i x := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold fullGradient; rw [smul_smul, mul_inv_cancel₀ hm', one_smul]

theorem grad_zero {n m : ℕ} {fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    fullGradient gs xstar = 0 := by
  obtain ⟨hF, _, hG⟩ := hfamily
  set G := ∑ i, gs i xstar with hGdef
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hm'' : (m:ℝ) ≠ 0 := hm'.ne'
  have hβ' : β ≠ 0 := hβ.ne'
  have hdesc : ∀ z, ∑ i, fs i z ≤
      ∑ i, fs i xstar + ⟪G, z - xstar⟫ + (m:ℝ) * (β / 2 * ‖z - xstar‖ ^ 2) := by
    intro z
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => svrg61_descent (hF i) (hG i) xstar z)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hminS : ∀ z, ∑ i, fs i xstar ≤ ∑ i, fs i z := by
    intro z; rw [obj_sum hm, obj_sum hm]; exact mul_le_mul_of_nonneg_left (hmin z) hm'.le
  set s : ℝ := 1 / ((m:ℝ) * β) with hsdef
  have hspos : 0 < s := by positivity
  have h1 := hdesc (xstar - s • G)
  have h2 := hminS (xstar - s • G)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos hspos, real_inner_self_eq_norm_sq] at h1
  have hs : (m:ℝ) * (β / 2 * (s * ‖G‖) ^ 2) = s / 2 * ‖G‖ ^ 2 := by
    rw [hsdef]; field_simp
  have hGn : ‖G‖ ^ 2 ≤ 0 := by nlinarith
  have hG2 : ‖G‖ ^ 2 = 0 := le_antisymm hGn (sq_nonneg _)
  have hG0 : G = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hG2)
  unfold fullGradient; rw [← hGdef, hG0, smul_zero]

theorem dir_sq_sum {n m : ℕ} {fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hF0 : fullGradient gs xstar = 0) (x y : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ‖direction gs x y i‖ ^ 2 ≤
      4 * β * (∑ i, fs i x - ∑ i, fs i xstar + (∑ i, fs i y - ∑ i, fs i xstar)) := by
  obtain ⟨hF, hc, hG⟩ := hfamily
  have hcoc : ∀ z, ∑ i, ‖gs i z - gs i xstar‖ ^ 2 ≤ 2 * β * (∑ i, fs i z - ∑ i, fs i xstar) := by
    intro z
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      svrg61_cocoercive hβ (hF i) (hG i) (hc i) xstar z)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← sum_inner,
      ← grad_sum hm, hF0, smul_zero, inner_zero_left, sub_zero] at this
    exact this
  set c := fullGradient gs y with hcdef
  have hsumb : ∑ i, (gs i y - gs i xstar) = (m:ℝ) • c := by
    rw [Finset.sum_sub_distrib, ← grad_sum hm, ← grad_sum hm, hF0, smul_zero, sub_zero]
  have hdir : ∀ i, direction gs x y i = (gs i x - gs i xstar) - ((gs i y - gs i xstar) - c) := by
    intro i; simp only [direction, hcdef]; abel
  have hpt : ∀ i, ‖direction gs x y i‖ ^ 2 ≤
      2 * ‖gs i x - gs i xstar‖ ^ 2 + 2 * ‖(gs i y - gs i xstar) - c‖ ^ 2 := by
    intro i; rw [hdir i]
    have h1 := norm_sub_sq_real (gs i x - gs i xstar) ((gs i y - gs i xstar) - c)
    have h2 := norm_add_sq_real (gs i x - gs i xstar) ((gs i y - gs i xstar) - c)
    nlinarith [sq_nonneg ‖(gs i x - gs i xstar) + ((gs i y - gs i xstar) - c)‖]
  have hvar : ∑ i, ‖(gs i y - gs i xstar) - c‖ ^ 2 ≤ ∑ i, ‖gs i y - gs i xstar‖ ^ 2 := by
    have e : ∀ i, ‖(gs i y - gs i xstar) - c‖ ^ 2 =
        ‖gs i y - gs i xstar‖ ^ 2 - 2 * ⟪gs i y - gs i xstar, c⟫ + ‖c‖ ^ 2 :=
      fun i => norm_sub_sq_real _ _
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsumb,
      real_inner_smul_left, real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (0:ℝ) ≤ m * ‖c‖ ^ 2 := by positivity
    linarith
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  have h1 := hcoc x
  have h2 := hcoc y
  linarith

theorem step_sum {n m : ℕ} {fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)}
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hF0 : fullGradient gs xstar = 0) (η : ℝ) (hη : 0 ≤ η) (x y : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ‖x - η • direction gs x y i - xstar‖ ^ 2 ≤
      (m:ℝ) * ‖x - xstar‖ ^ 2 - 2 * η * (∑ i, fs i x - ∑ i, fs i xstar) +
        η ^ 2 * (4 * β * (∑ i, fs i x - ∑ i, fs i xstar + (∑ i, fs i y - ∑ i, fs i xstar))) := by
  have e : ∀ i, ‖x - η • direction gs x y i - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪direction gs x y i, x - xstar⟫ +
        η ^ 2 * ‖direction gs x y i‖ ^ 2 := by
    intro i
    have : x - η • direction gs x y i - xstar = (x - xstar) - η • direction gs x y i := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← sum_inner]
  have hsd : ∑ i, direction gs x y i = ∑ i, gs i x := by
    simp only [direction]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, grad_sum hm]
    abel
  rw [hsd, sum_inner]
  have hlin : ∑ i, fs i x - ∑ i, fs i xstar ≤ ∑ i, ⟪gs i x, x - xstar⟫ := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_le_sum; intro i _
    have := svrg61_convex_fo (hfamily.1 i) (hfamily.2.1 i) x xstar
    have h2 : ⟪gs i x, xstar - x⟫ = -⟪gs i x, x - xstar⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  have hq := dir_sq_sum hm hβ hfamily hF0 x y
  have h3 := mul_le_mul_of_nonneg_left hlin (by positivity : (0:ℝ) ≤ 2 * η)
  have h4 := mul_le_mul_of_nonneg_left hq (sq_nonneg η)
  linarith

end SVRG61Help

open ConvexOptAlg.SVRG in open scoped InnerProductSpace in
theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β η : ℝ) (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hη : 0 ≤ η)
    (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun i : Fin m => ‖(x - η • direction gs x y i) - xstar‖ ^ 2) ≤
      ‖x - xstar‖ ^ 2 -
        2 * η * (1 - 2 * β * η) * (objective fs x - objective fs xstar) +
        4 * β * η ^ 2 * (objective fs y - objective fs xstar) := by
  have hF0 := SVRG61Help.grad_zero hm hβ hfamily hmin
  have h := SVRG61Help.step_sum hm hβ hfamily hF0 η hη x y
  rw [SVRG61Help.obj_sum hm fs x, SVRG61Help.obj_sum hm fs y,
    SVRG61Help.obj_sum hm fs xstar] at h
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [uniformMean, Fintype.card_fin, div_le_iff₀ hm']
  calc _ ≤ _ := h
    _ = _ := by ring
