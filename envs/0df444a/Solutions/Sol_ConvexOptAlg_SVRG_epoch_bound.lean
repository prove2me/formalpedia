-- Prove2me | solution 1 for ConvexOptAlg.SVRG.epoch_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:32:11.084229+00:00
-- url     : https://prove2.me/submissions/83d8e018-e3b2-423b-ab1d-12e5f350bea6

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace
open scoped RealInnerProductSpace

namespace ConvexOptAlg.SVRG

lemma sg_line {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (g' : EuclideanSpace ℝ (Fin d))
    (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) (hg : HasGradientAt g g' (x + t • v)) :
    HasDerivAt (fun s : ℝ => g (x + s • v)) ⟪g', v⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have := hg.hasFDerivAt.comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at this
  exact this

lemma sg_strong_lower {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (μ : ℝ)
    (g' : EuclideanSpace ℝ (Fin d)) (x w : EuclideanSpace ℝ (Fin d))
    (hconv : StrongConvexOn Set.univ μ g) (hgrad : HasGradientAt g g' x) :
    g x + ⟪g', w - x⟫ + μ / 2 * ‖w - x‖ ^ 2 ≤ g w := by
  set r := w - x with hr
  have hφ := strongConvexOn_iff_convex.mp hconv
  set ψ : ℝ → ℝ := fun s => g (x + s • r) - μ / 2 * (‖x‖ ^ 2 + 2 * s * ⟪x, r⟫ + s ^ 2 * ‖r‖ ^ 2)
    with hψ
  have hψeq : ∀ s : ℝ, ψ s = g (x + s • r) - μ / (2:ℝ) * ‖x + s • r‖ ^ 2 := by
    intro s
    simp only [hψ]
    rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hψconv : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ p q hp hq hpq
    have e : x + (p • a + q • b) • r = p • (x + a • r) + q • (x + b • r) := by
      obtain rfl : q = 1 - p := by linarith
      simp only [smul_eq_mul]
      module
    rw [hψeq, hψeq, hψeq, e]
    exact hφ.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
  have hd1 : HasDerivAt (fun s : ℝ => g (x + s • r)) ⟪g', r⟫ 0 :=
    sg_line g g' x r 0 (by simpa using hgrad)
  have hd2 : HasDerivAt (fun s : ℝ => μ / 2 * (‖x‖ ^ 2 + 2 * s * ⟪x, r⟫ + s ^ 2 * ‖r‖ ^ 2))
      (μ / 2 * (2 * ⟪x, r⟫ + 2 * 0 * ‖r‖ ^ 2)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s * ⟪x, r⟫) (2 * ⟪x, r⟫) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ⟪x, r⟫
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * ‖r‖ ^ 2) (2 * 0 * ‖r‖ ^ 2) 0 := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).mul_const (‖r‖ ^ 2)
    exact (((hasDerivAt_const (0:ℝ) (‖x‖ ^ 2)).add h1).add h2).const_mul (μ / 2) |>.congr_deriv
      (by ring)
  have hd : HasDerivAt ψ (⟪g', r⟫ - μ / 2 * (2 * ⟪x, r⟫ + 2 * 0 * ‖r‖ ^ 2)) 0 := hd1.sub hd2
  have hs := hψconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    zero_lt_one hd
  rw [slope_def_field] at hs
  simp only [hψ] at hs
  have e1 : x + (1:ℝ) • r = w := by simp [hr]
  have e0 : x + (0:ℝ) • r = x := by simp
  rw [e1, e0] at hs
  norm_num at hs
  nlinarith

lemma sg_grad_ineq {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d)) (x w : EuclideanSpace ℝ (Fin d))
    (hconv : ConvexOn ℝ Set.univ g) (hgrad : HasGradientAt g g' x) :
    g x + ⟪g', w - x⟫ ≤ g w := by
  have := sg_strong_lower g 0 g' x w (strongConvexOn_zero.mpr hconv) hgrad
  simpa using this

lemma sg_descent {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ x, HasGradientAt g (g' x) x) (L : ℝ)
    (hL : ∀ x y, ‖g' x - g' y‖ ≤ L * ‖x - y‖) (x y : EuclideanSpace ℝ (Fin d)) :
    g y ≤ g x + ⟪g' x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun t => g (x + t • v) - t * ⟪g' x, v⟫ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (⟪g' (x + t • v), v⟫ - ⟪g' x, v⟫ - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := sg_line g (g' (x + t • v)) x v t (hgrad _)
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪g' x, v⟫) ⟪g' x, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪g' x, v⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := (hp.const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hcs : ⟪g' (x + t • v) - g' x, v⟫ ≤
          ‖g' (x + t • v) - g' x‖ * ‖v‖ := real_inner_le_norm _ _
      have hlip := hL (x + t • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

/-- generalized cocoercivity, multiplied form. -/
lemma sg_cocoer {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (μ L : ℝ)
    (hlow : ∀ x w, g x + ⟪g' x, w - x⟫ + μ / 2 * ‖w - x‖ ^ 2 ≤ g w)
    (hup : ∀ x w, g w ≤ g x + ⟪g' x, w - x⟫ + L / 2 * ‖w - x‖ ^ 2)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖g' y - g' x - μ • (y - x)‖ ^ 2 ≤
      2 * (L - μ) * (g y - g x - ⟪g' x, y - x⟫ - μ / 2 * ‖y - x‖ ^ 2) := by
  set r := y - x with hr
  set z := g' y - g' x - μ • r with hz
  set D := g y - g x - ⟪g' x, r⟫ - μ / 2 * ‖r‖ ^ 2 with hD
  set M := L - μ with hM
  have key : ∀ t : ℝ, t * ‖z‖ ^ 2 - M / 2 * t ^ 2 * ‖z‖ ^ 2 ≤ D := by
    intro t
    have h1 := hlow x (y - t • z)
    have h2 := hup y (y - t • z)
    have e1 : y - t • z - x = r - t • z := by simp only [hr]; abel
    have e2 : y - t • z - y = -(t • z) := by abel
    rw [e1] at h1
    rw [e2] at h2
    rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_neg_right,
      inner_smul_right] at h2
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
      inner_sub_right, inner_smul_right] at h1
    have hzz : ⟪g' y, z⟫ - ⟪g' x, z⟫ - μ * ⟪r, z⟫ = ‖z‖ ^ 2 := by
      have : ‖z‖ ^ 2 = ⟪g' y - g' x - μ • r, z⟫ := by rw [← hz, real_inner_self_eq_norm_sq]
      rw [this]; simp only [inner_sub_left, real_inner_smul_left]
    have ht := congrArg (fun q => t * q) hzz
    rw [hD, hM]
    nlinarith
  have hD0 : 0 ≤ D := by simpa using key 0
  rcases lt_trichotomy M 0 with hneg | hzero | hpos
  · -- then r = 0
    have hup' : g y ≤ g x + ⟪g' x, r⟫ + L / 2 * ‖r‖ ^ 2 := hup x y
    have hDle : D ≤ M / 2 * ‖r‖ ^ 2 := by rw [hD, hM]; linarith
    have hr0 : ‖r‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖r‖]
    have hr0' : r = 0 := by
      have : ‖r‖ = 0 := by nlinarith [norm_nonneg r]
      exact norm_eq_zero.mp this
    have hyx : y = x := by rw [hr] at hr0'; exact sub_eq_zero.mp hr0'
    have hz0 : z = 0 := by simp [hz, hr0', hyx]
    have hD00 : D = 0 := by rw [hr0] at hDle; linarith
    rw [hz0, hD00]; simp
  · rw [hzero]
    by_contra hcon
    push_neg at hcon
    have hZ : 0 < ‖z‖ ^ 2 := by nlinarith
    have := key ((D + 1) / ‖z‖ ^ 2)
    rw [hzero] at this
    have e : (D + 1) / ‖z‖ ^ 2 * ‖z‖ ^ 2 = D + 1 := div_mul_cancel₀ _ hZ.ne'
    simp only [zero_div, zero_mul, sub_zero] at this
    linarith
  · have h := key (1 / M)
    have e : 1 / M * ‖z‖ ^ 2 - M / 2 * (1 / M) ^ 2 * ‖z‖ ^ 2 = ‖z‖ ^ 2 / (2 * M) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at h
    linarith

lemma sv_mF {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin n)) : (m:ℝ) * objective fs x = ∑ i, fs i x := by
  have : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [objective, uniformMean, Fintype.card_fin]
  field_simp

lemma sv_sumg {n m : ℕ} (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, gs i x = (m:ℝ) • fullGradient gs x := by
  have : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [fullGradient, smul_smul, mul_inv_cancel₀ this, one_smul]

lemma sv_minner {n m : ℕ} (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (x v : EuclideanSpace ℝ (Fin n)) :
    (m:ℝ) * ⟪fullGradient gs x, v⟫ = ∑ i, ⟪gs i x, v⟫ := by
  rw [← sum_inner, sv_sumg gs hm, real_inner_smul_left]

lemma sv_lower {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hm : 0 < m) (hfamily : SmoothConvexFamily fs gs β) (x w : EuclideanSpace ℝ (Fin n)) :
    objective fs x + ⟪fullGradient gs x, w - x⟫ ≤ objective fs w := by
  have hM : (0:ℝ) < m := by exact_mod_cast hm
  have per : ∀ i ∈ Finset.univ, fs i x + ⟪gs i x, w - x⟫ ≤ fs i w := fun i _ =>
    sg_grad_ineq (fs i) (gs i x) x w (hfamily.2.1 i) (hfamily.1 i x)
  have hs := Finset.sum_le_sum per
  rw [Finset.sum_add_distrib, ← sv_mF fs hm, ← sv_mF fs hm, ← sv_minner gs hm] at hs
  have : (m:ℝ) * (objective fs x + ⟪fullGradient gs x, w - x⟫) ≤ m * objective fs w := by
    linarith
  exact le_of_mul_le_mul_left this hM

lemma sv_upper {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (hm : 0 < m) (hfamily : SmoothConvexFamily fs gs β) (x w : EuclideanSpace ℝ (Fin n)) :
    objective fs w ≤ objective fs x + ⟪fullGradient gs x, w - x⟫ + β / 2 * ‖w - x‖ ^ 2 := by
  have hM : (0:ℝ) < m := by exact_mod_cast hm
  have per : ∀ i ∈ Finset.univ,
      fs i w ≤ fs i x + ⟪gs i x, w - x⟫ + β / 2 * ‖w - x‖ ^ 2 := fun i _ =>
    sg_descent (fs i) (gs i) (hfamily.1 i) β (hfamily.2.2 i) x w
  have hs := Finset.sum_le_sum per
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sv_mF fs hm, ← sv_mF fs hm,
    ← sv_minner gs hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have : (m:ℝ) * objective fs w ≤
      m * (objective fs x + ⟪fullGradient gs x, w - x⟫ + β / 2 * ‖w - x‖ ^ 2) := by
    linarith
  exact le_of_mul_le_mul_left this hM

lemma sv_grad_zero {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    fullGradient gs xstar = 0 := by
  set G := fullGradient gs xstar with hG
  have h1 := sv_upper fs gs β hm hfamily xstar (xstar - (1 / β) • G)
  have h2 := hmin (xstar - (1 / β) • G)
  have e : xstar - (1 / β) • G - xstar = -((1 / β) • G) := by abel
  rw [e, norm_neg, norm_smul, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow] at h1
  have h3 : ‖G‖ ^ 2 * (1 / β) ≤ 0 := by
    have : (1 / β) ^ 2 * β = 1 / β := by field_simp
    nlinarith
  have h4 : ‖G‖ ^ 2 ≤ 0 := by
    have hb : 0 < 1 / β := by positivity
    nlinarith
  have : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
  exact norm_eq_zero.mp this

lemma sv_sum_star {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    ∑ i, gs i xstar = 0 := by
  rw [sv_sumg gs hm, sv_grad_zero fs gs β xstar hm hβ hfamily hmin, smul_zero]

lemma sv_64 {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    ∑ i, ‖gs i x - gs i xstar‖ ^ 2 ≤
      2 * β * (m * (objective fs x - objective fs xstar)) := by
  have per : ∀ i ∈ Finset.univ, ‖gs i x - gs i xstar‖ ^ 2 ≤
      2 * β * (fs i x - fs i xstar) - 2 * β * ⟪gs i xstar, x - xstar⟫ := by
    intro i _
    have hc := sg_cocoer (fs i) (gs i) 0 β
      (fun a b => by
        simpa using sg_grad_ineq (fs i) (gs i a) a b (hfamily.2.1 i) (hfamily.1 i a))
      (fun a b => sg_descent (fs i) (gs i) (hfamily.1 i) β (hfamily.2.2 i) a b) xstar x
    simp only [zero_smul, sub_zero, zero_div, zero_mul] at hc
    linarith
  have hs := Finset.sum_le_sum per
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← sum_inner, sv_sum_star fs gs β xstar hm hβ hfamily hmin, inner_zero_left,
    ← sv_mF fs hm, ← sv_mF fs hm] at hs
  linarith

lemma sv_var {d n : ℕ} (hn : 0 < n) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∑ j, ‖a j - (1 / (n:ℝ)) • ∑ i, a i‖ ^ 2 ≤ ∑ j, ‖a j‖ ^ 2 := by
  set m := (1 / (n:ℝ)) • ∑ i, a i with hm
  have hN : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ∑ i, a i = (n:ℝ) • m := by
    rw [hm, smul_smul, mul_one_div_cancel hN, one_smul]
  have e : ∀ j, ‖a j - m‖ ^ 2 = ‖a j‖ ^ 2 - 2 * ⟪a j, m⟫ + ‖m‖ ^ 2 := fun j => norm_sub_sq_real _ _
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← sum_inner]
  rw [hs, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have : (0:ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg ‖m‖]

lemma sv_sq2 {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [norm_sub_sq_real u v, norm_add_sq_real u v, sq_nonneg ‖u + v‖]

lemma sv_63 {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    ∑ i, ‖direction gs x y i‖ ^ 2 ≤
      4 * β * (m * (objective fs x - objective fs xstar +
        objective fs y - objective fs xstar)) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set u : Fin m → EuclideanSpace ℝ (Fin n) := fun i => gs i y - gs i xstar with hu
  have hub : (1 / (m:ℝ)) • ∑ i, u i = fullGradient gs y := by
    simp only [hu, Finset.sum_sub_distrib, sv_sum_star fs gs β xstar hm hβ hfamily hmin,
      sub_zero, fullGradient, one_div]
  have hd : ∀ i, direction gs x y i =
      (gs i x - gs i xstar) - (u i - (1 / (m:ℝ)) • ∑ j, u j) := by
    intro i
    rw [hub]; simp only [direction, hu]; abel
  have per : ∀ i ∈ Finset.univ, ‖direction gs x y i‖ ^ 2 ≤
      2 * ‖gs i x - gs i xstar‖ ^ 2 + 2 * ‖u i - (1 / (m:ℝ)) • ∑ j, u j‖ ^ 2 := by
    intro i _; rw [hd]; exact sv_sq2 _ _
  have hs := Finset.sum_le_sum per
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hv := sv_var hm u
  have h1 := sv_64 fs gs β x xstar hm hβ hfamily hmin
  have h2 := sv_64 fs gs β y xstar hm hβ hfamily hmin
  simp only [hu] at hv
  nlinarith

lemma sv_unb {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x y v : EuclideanSpace ℝ (Fin n)) (hm : 0 < m) :
    ∑ i, ⟪direction gs x y i, v⟫ = m * ⟪fullGradient gs x, v⟫ := by
  simp only [direction, inner_add_left, inner_sub_left, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← sv_minner gs hm, ← sv_minner gs hm]
  ring

lemma sv_onestep {n m : ℕ} (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β η : ℝ)
    (x y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hβ : 0 < β) (hη : 0 ≤ η) (hfamily : SmoothConvexFamily fs gs β)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    ∑ i, ‖(x - η • direction gs x y i) - xstar‖ ^ 2 ≤
      m * (‖x - xstar‖ ^ 2 - 2 * η * (1 - 2 * β * η) * (objective fs x - objective fs xstar) +
        4 * β * η ^ 2 * (objective fs y - objective fs xstar)) := by
  have e : ∀ i, ‖(x - η • direction gs x y i) - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪direction gs x y i, x - xstar⟫ +
        η ^ 2 * ‖direction gs x y i‖ ^ 2 := by
    intro i
    have : (x - η • direction gs x y i) - xstar = (x - xstar) - η • direction gs x y i := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm]
    ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [sv_unb gs x y _ hm]
  have h63 := sv_63 fs gs β x y xstar hm hβ hfamily hmin
  have hl := sv_lower fs gs β hm hfamily x xstar
  have ei : ⟪fullGradient gs x, xstar - x⟫ = -⟪fullGradient gs x, x - xstar⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [ei] at hl
  have hM : (0:ℝ) ≤ m := by positivity
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have k1 := mul_le_mul_of_nonneg_left h63 hη2
  have k2 : 2 * η * (m * (objective fs x - objective fs xstar)) ≤
      2 * η * (m * ⟪fullGradient gs x, x - xstar⟫) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hM) (by linarith)
  nlinarith

lemma sv_iter_update {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) (t : Fin k) (i : Fin m) :
    ∀ s, s ≤ t.val → innerIter gs η y (Function.update idx t i) s = innerIter gs η y idx s := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s < k := by omega
    rw [innerIter, innerIter, dif_pos hs', dif_pos hs', ih (by omega)]
    have hne : (⟨s, hs'⟩ : Fin k) ≠ t := by
      intro h; rw [← h] at hs; simp at hs
    rw [Function.update_of_ne hne]

lemma sv_iter_succ {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) (t : Fin k) :
    innerIter gs η y idx (t.val + 1) =
      innerIter gs η y idx t.val - η • direction gs (innerIter gs η y idx t.val) y (idx t) := by
  rw [innerIter, dif_pos t.isLt]

lemma sv_sum_update {m k : ℕ} (G : (Fin k → Fin m) → ℝ) (t : Fin k) :
    ∑ idx, ∑ i, G (Function.update idx t i) = (m:ℝ) * ∑ idx, G idx := by
  set e := Equiv.piSplitAt t (fun _ => Fin m) with he
  have hupd : ∀ idx i, Function.update idx t i = e.symm (i, (e idx).2) := by
    intro idx i
    apply e.injective
    rw [Equiv.apply_symm_apply]
    ext j
    · simp [he, Equiv.piSplitAt_apply]
    · simp [he, Equiv.piSplitAt_apply, Function.update_of_ne j.2]
  simp only [hupd]
  rw [Fintype.sum_equiv e (fun idx => ∑ i, G (e.symm (i, (e idx).2)))
    (fun p => ∑ i, G (e.symm (i, p.2))) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

lemma sv_step_avg {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (t : Fin k) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    (m:ℝ) * ∑ idx : Fin k → Fin m, h (innerIter gs η y idx (t.val + 1)) =
      ∑ idx : Fin k → Fin m, ∑ i, h (innerIter gs η y idx t.val -
        η • direction gs (innerIter gs η y idx t.val) y i) := by
  rw [← sv_sum_update (fun idx => h (innerIter gs η y idx (t.val + 1))) t]
  apply Finset.sum_congr rfl
  intro idx _
  apply Finset.sum_congr rfl
  intro i _
  rw [sv_iter_succ, sv_iter_update gs η y idx t i t.val le_rfl, Function.update_self]

theorem epoch_bound_core {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β η : ℝ) (k : ℕ) (y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hα : 0 < α) (hβ : 0 < β)
    (hη : 0 < η) (hηsmall : 2 * β * η < 1)
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin k → Fin m => objective fs (epochOut gs η k y idx)) -
        objective fs xstar ≤
      (1 / (α * η * (1 - 2 * β * η) * (k : ℝ)) +
        2 * β * η / (1 - 2 * β * η)) *
        (objective fs y - objective fs xstar) := by
  set F := objective fs with hF
  set Fs := objective fs xstar with hFs
  set D := F y - Fs with hD
  set c := 2 * η * (1 - 2 * β * η) with hc
  set B := 4 * β * η ^ 2 * D with hB
  set N : ℝ := (Fintype.card (Fin k → Fin m) : ℝ) with hN
  have hM : (0:ℝ) < m := by exact_mod_cast hm
  have hK : (0:ℝ) < k := by exact_mod_cast hk
  have hNpos : 0 < N := by
    rw [hN]; have : Nonempty (Fin k → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
    exact_mod_cast Fintype.card_pos
  have hD0 : 0 ≤ D := by rw [hD]; linarith [hmin y]
  have hc0 : 0 < c := by rw [hc]; have : 0 < 1 - 2 * β * η := by linarith
                         positivity
  set X : (Fin k → Fin m) → ℕ → EuclideanSpace ℝ (Fin n) := fun idx s => innerIter gs η y idx s
    with hX
  set S : ℕ → ℝ := fun s => ∑ idx, ‖X idx s - xstar‖ ^ 2 with hS
  set A : ℕ → ℝ := fun s => ∑ idx, (F (X idx s) - Fs) with hA
  -- one step
  have step : ∀ t : Fin k, S (t.val + 1) ≤ S t.val - c * A t.val + N * B := by
    intro t
    have h1 := sv_step_avg gs η y t (fun z => ‖z - xstar‖ ^ 2)
    have h2 : ∀ idx ∈ Finset.univ, ∑ i, ‖(X idx t.val - η • direction gs (X idx t.val) y i)
        - xstar‖ ^ 2 ≤ m * (‖X idx t.val - xstar‖ ^ 2 - c * (F (X idx t.val) - Fs) + B) :=
      fun idx _ => sv_onestep fs gs β η (X idx t.val) y xstar hm hβ hη.le hfamily hmin
    have h3 := Finset.sum_le_sum h2
    rw [← Finset.mul_sum] at h3
    have h4 : ∑ idx : Fin k → Fin m, (‖X idx t.val - xstar‖ ^ 2 - c * (F (X idx t.val) - Fs) + B)
        = S t.val - c * A t.val + N * B := by
      simp only [hS, hA, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
    rw [h4] at h3
    have h5 : (m:ℝ) * S (t.val + 1) ≤ m * (S t.val - c * A t.val + N * B) := by
      simp only [hS, hX]; simp only [hX] at h3; linarith
    exact le_of_mul_le_mul_left h5 hM
  have tele : ∀ s, s ≤ k → S s + c * ∑ t ∈ Finset.range s, A t ≤ S 0 + s * (N * B) := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      have := step ⟨s, by omega⟩
      have := ih (by omega)
      simp only [Finset.sum_range_succ] at *
      push_cast
      nlinarith
  have hT := tele k le_rfl
  have hSk : 0 ≤ S k := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hgz := sv_grad_zero fs gs β xstar hm hβ hfamily hmin
  have hyx : ‖y - xstar‖ ^ 2 ≤ 2 / α * D := by
    have := hstrong xstar (Set.mem_univ _) y (Set.mem_univ _)
    rw [hgz, inner_zero_left] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    rw [hD]; linarith
  have hS0 : S 0 = N * ‖y - xstar‖ ^ 2 := by
    simp only [hS, hX, innerIter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  -- Jensen
  have jensen : ∀ idx, (k:ℝ) * F (epochOut gs η k y idx) ≤ ∑ t : Fin k, F (X idx t.val) := by
    intro idx
    set z := epochOut gs η k y idx with hz
    have per : ∀ t ∈ (Finset.univ : Finset (Fin k)),
        F z + ⟪fullGradient gs z, X idx t.val - z⟫ ≤ F (X idx t.val) :=
      fun t _ => sv_lower fs gs β hm hfamily z _
    have hs := Finset.sum_le_sum per
    rw [Finset.sum_add_distrib, ← inner_sum, Finset.sum_sub_distrib] at hs
    have e0 : ∑ t : Fin k, X idx t.val - ∑ _t : Fin k, z = 0 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hz, epochOut,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hK.ne', one_smul]
      simp [hX]
    rw [e0, inner_zero_right, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
    linarith
  set P := ∑ idx, F (epochOut gs η k y idx) - N * Fs with hP
  have hkP : (k:ℝ) * P ≤ ∑ t ∈ Finset.range k, A t := by
    have h1 := Finset.sum_le_sum (fun idx (_ : idx ∈ Finset.univ) => jensen idx)
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ t ∈ Finset.range k, A t = ∑ idx, ∑ t : Fin k, F (X idx t.val) - k * (N * Fs) := by
      rw [Finset.sum_range (fun t => A t)]
      simp only [hA, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fin, hN]
      rw [Finset.sum_comm]
    rw [h2, hP]; nlinarith
  have hfin : c * (k * P) ≤ N * (2 / α * D) + k * (N * B) := by
    have := mul_le_mul_of_nonneg_left hkP hc0.le
    have := mul_le_mul_of_nonneg_left hyx hNpos.le
    nlinarith
  have hU : uniformMean (fun idx : Fin k → Fin m => F (epochOut gs η k y idx)) - Fs = P / N := by
    simp only [uniformMean, hP, hN]
    field_simp
  rw [hU, div_le_iff₀ hNpos]
  have h1m : 0 < 1 - 2 * β * η := by linarith
  have e : (1 / (α * η * (1 - 2 * β * η) * (k : ℝ)) + 2 * β * η / (1 - 2 * β * η)) * D * N
      * (c * k) = N * (2 / α * D) + k * (N * B) := by
    rw [hc, hB]
    set q := 1 - 2 * β * η with hq
    have hq0 : q ≠ 0 := h1m.ne'
    have hβη : 2 * β * η = 1 - q := by rw [hq]; ring
    field_simp
    ring
  have hck : 0 < c * k := by positivity
  rw [← e] at hfin
  have : P * (c * k) ≤ (1 / (α * η * (1 - 2 * β * η) * (k : ℝ)) + 2 * β * η / (1 - 2 * β * η))
      * D * N * (c * k) := by linarith
  exact le_of_mul_le_mul_right this hck

end ConvexOptAlg.SVRG

open ConvexOptAlg.SVRG


theorem solution {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β η : ℝ) (k : ℕ) (y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hα : 0 < α) (hβ : 0 < β)
    (hη : 0 < η) (hηsmall : 2 * β * η < 1)
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin k → Fin m => objective fs (epochOut gs η k y idx)) -
        objective fs xstar ≤
      (1 / (α * η * (1 - 2 * β * η) * (k : ℝ)) +
        2 * β * η / (1 - 2 * β * η)) *
        (objective fs y - objective fs xstar) := by
  exact epoch_bound_core fs gs α β η k y xstar hm hk hα hβ hη hηsmall hfamily hstrong hmin
