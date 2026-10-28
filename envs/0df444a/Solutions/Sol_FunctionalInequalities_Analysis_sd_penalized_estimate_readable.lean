-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sd_penalized_estimate_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:52.441207+00:00
-- url     : https://prove2.me/submissions/120267d6-6a75-4337-9f16-43fd6f1c41be

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

noncomputable section
open scoped RealInnerProductSpace
section LT17CPenalizedMaximumBound
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.sd_support [FiniteDimensional ℝ E] {f : E → ℝ}
    (hc : ConvexOn ℝ univ f) (hf : Differentiable ℝ f) (x y : E) :
    fderiv ℝ f x (y - x) ≤ f y - f x := by
  have hp : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
    simpa only [zero_smul, add_zero] using (hf x).hasFDerivAt
  have hl := hd.comp_hasDerivAt 0 hp
  have hc' : ConvexOn ℝ univ (fun t : ℝ => f (x + t • (y - x))) := by
    simpa only [Set.preimage_univ, Function.comp_def,
      AffineMap.lineMap_apply_module', add_comm] using
      hc.comp_affineMap (AffineMap.lineMap x y)
  simpa only [slope_def_field, zero_smul, add_zero, one_smul,
    add_sub_cancel, sub_zero, div_one] using
    hc'.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hl
private lemma FunctionalInequalities.Analysis.sd_stationary [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Differentiable ℝ u) (x h : E) (η : ℝ)
    (hm : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
      u (x + h) + u (x - h) - 2 * u x - η * u x) :
    gradient u (x + h) + gradient u (x - h) - (2 : ℝ) • gradient u x =
      η • gradient u x := by
  let T := InnerProductSpace.toDual ℝ E
  have ha : HasFDerivAt (fun y => u (y + h))
      (T (gradient u (x + h))) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      ((hu (x + h)).hasGradientAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const h))
  have hb : HasFDerivAt (fun y => u (y - h))
      (T (gradient u (x - h))) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((hu (x - h)).hasGradientAt.hasFDerivAt.comp x
        (hasFDerivAt_sub_const h))
  have hd := ((ha.add hb).sub
    ((hu x).hasGradientAt.hasFDerivAt.const_mul 2)).sub
      ((hu x).hasGradientAt.hasFDerivAt.const_mul η)
  have hm' : IsLocalMax
      (fun y => u (y + h) + u (y - h) - 2 * u y - η * u y) x :=
    Filter.Eventually.of_forall hm
  have hz := hm'.hasFDerivAt_eq_zero hd
  apply ext_inner_right ℝ
  intro v
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hz
  simp only [T, add_apply, sub_apply, smul_apply, smul_eq_mul,
    zero_apply, InnerProductSpace.toDual_apply_apply] at he
  simpa only [inner_sub_left, inner_add_left, real_inner_smul_left] using
    (sub_eq_zero.mp he)
private lemma FunctionalInequalities.Analysis.sd_midpoint {V : E → ℝ} {κ : ℝ}
    (hs : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (p w : E) :
    κ * ‖w‖ ^ 2 ≤ V (p + w) + V (p - w) - 2 * V p := by
  have he : (1 / 2 : ℝ) • (p + w) + (1 / 2 : ℝ) • (p - w) = p := by
    module
  have hc := hs.2 (mem_univ (p + w)) (mem_univ (p - w))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [he] at hc
  simp only [smul_eq_mul, norm_add_sq_real, norm_sub_sq_real] at hc
  nlinarith
private lemma FunctionalInequalities.Analysis.sd_quadratic (κ q H B : ℝ) (hk : 0 < κ)
    (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hq : κ * q ^ 2 ≤ 2 * H * q + B) :
    q ≤ 2 * H / κ + Real.sqrt (B / κ) := by
  have hs := Real.sq_sqrt (div_nonneg hB hk.le)
  have hp := Real.sqrt_nonneg (B / κ)
  have hd : 0 ≤ 2 * H / κ := div_nonneg (by positivity) hk.le
  have he : κ * (2 * H / κ) = 2 * H := by
    field_simp
  have hb : κ * (B / κ) = B := by
    field_simp
  by_contra hn
  have hh : 2 * H / κ + Real.sqrt (B / κ) < q := lt_of_not_ge hn
  have hprod := mul_pos (sub_pos.mpr hh)
    (show 0 < q - 2 * H / κ + Real.sqrt (B / κ) by linarith)
  have hquad : q ^ 2 ≤ (2 * H / κ) * q + B / κ := by
    nlinarith
  nlinarith [mul_nonneg hd (show 0 ≤ q - 2 * H / κ by linarith)]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
set_option maxHeartbeats 800000 in
 lemma solution {u V : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
    (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    {C : ℝ} (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C)
    (n : ℕ) (h x₀ : E) {η : ℝ} (hη : 0 < η)
    (hmaximum : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
      u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀)
    (hcomparison :
      (V (gradient u (x₀ + h)) - u (x₀ + h)) +
        (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    u (x₀ + h) + u (x₀ - h) - 2 * u x₀ ≤
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * (n + C) / κ) := by
  let a := gradient u (x₀ + h)
  let b := gradient u (x₀ - h)
  let c := gradient u x₀
  let p := (1 / 2 : ℝ) • (a + b)
  let w := (1 / 2 : ℝ) • (a - b)
  let D := u (x₀ + h) + u (x₀ - h) - 2 * u x₀

  have hstationary : a + b - (2 : ℝ) • c = η • c :=
    FunctionalInequalities.Analysis.sd_stationary hu x₀ h η hmaximum
  have hp : p - c = (η / 2) • c := by
    have ht : p - c = (1 / 2 : ℝ) • (a + b - (2 : ℝ) • c) := by
      dsimp [p]
      module
    rw [ht, hstationary]
    module

  have ha := FunctionalInequalities.Analysis.sd_support hconv hu (x₀ + h) x₀
  have hb := FunctionalInequalities.Analysis.sd_support hconv hu (x₀ - h) x₀
  rw [show x₀ - (x₀ + h) = -h by abel,
    (hu (x₀ + h)).hasGradientAt.hasFDerivAt.fderiv,
    InnerProductSpace.toDual_apply_apply] at ha
  rw [show x₀ - (x₀ - h) = h by abel,
    (hu (x₀ - h)).hasGradientAt.hasFDerivAt.fderiv,
    InnerProductSpace.toDual_apply_apply] at hb
  change ⟪a, -h⟫ ≤ u x₀ - u (x₀ + h) at ha
  change ⟪b, h⟫ ≤ u x₀ - u (x₀ - h) at hb
  have hn : ‖w‖ = (1 / 2 : ℝ) * ‖a - b‖ := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hD : D ≤ 2 * ‖h‖ * ‖w‖ := by
    have hi := real_inner_le_norm (a - b) h
    rw [inner_sub_left] at hi
    rw [inner_neg_right] at ha
    dsimp [D]
    rw [hn]
    nlinarith only [ha, hb, hi]

  have hconvV : ConvexOn ℝ univ V := by
    have hn' : ConvexOn ℝ univ (fun y : E => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he :
        (fun y => V y - κ / 2 * ‖y‖ ^ 2) +
          (fun y => (κ / 2) • ‖y‖ ^ 2) = V := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hpa : p + w = a := by
    dsimp [p, w]
    module
  have hpb : p - w = b := by
    dsimp [p, w]
    module
  have hmid := FunctionalInequalities.Analysis.sd_midpoint hstrong p w
  rw [hpa, hpb] at hmid
  have hs := FunctionalInequalities.Analysis.sd_support hconvV hV c p
  rw [hp, map_smul, smul_eq_mul] at hs
  have hc : -C ≤ fderiv ℝ V c c :=
    (neg_le_neg (hC x₀)).trans (neg_abs_le _)
  have he := mul_le_mul_of_nonneg_left hc hη.le
  have hcomp : V a + V b - 2 * V c ≤ D + η * (n : ℝ) := by
    dsimp [a, b, c, D]
    linarith only [hcomparison]
  have hgap : κ * ‖w‖ ^ 2 ≤ D + η * ((n : ℝ) + C) := by
    nlinarith only [hmid, hs, he, hcomp]
  have hCnonneg : 0 ≤ C :=
    (abs_nonneg (fderiv ℝ V (gradient u x₀) (gradient u x₀))).trans (hC x₀)
  have hB : 0 ≤ η * ((n : ℝ) + C) := by
    positivity
  have hquad : κ * ‖w‖ ^ 2 ≤
      2 * ‖h‖ * ‖w‖ + η * ((n : ℝ) + C) := by
    linarith only [hgap, hD]
  have hq := FunctionalInequalities.Analysis.sd_quadratic κ ‖w‖ ‖h‖ (η * ((n : ℝ) + C))
    hκ (norm_nonneg h) hB hquad
  have ht := hD.trans (mul_le_mul_of_nonneg_left hq
    (show 0 ≤ 2 * ‖h‖ by positivity))
  have he' :
      2 * ‖h‖ * (2 * ‖h‖ / κ + Real.sqrt (η * ((n : ℝ) + C) / κ)) =
        4 * ‖h‖ ^ 2 / κ +
          2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) := by
    ring
  rw [he'] at ht
  exact ht
