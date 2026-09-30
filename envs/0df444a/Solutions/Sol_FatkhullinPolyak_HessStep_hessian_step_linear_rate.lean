-- Prove2me | solution 1 for FatkhullinPolyak.HessStep.hessian_step_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:51:41.356968+00:00
-- url     : https://prove2.me/submissions/f9e3c016-6b19-4dc4-8631-8421e9bc5cd1

import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
open FatkhullinPolyak.HessStep Filter Topology
open scoped RealInnerProductSpace

private theorem strong_first {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hc : StrongConvexOn Set.univ μ f) (x y : EuclideanSpace ℝ (Fin n)) :
    f x+⟪gradient f x,y-x⟫+μ/2*‖y-x‖^2 ≤ f y := by
  let q:=fun z => f z-μ/2*‖z‖^2
  have hq : ConvexOn ℝ Set.univ q := strongConvexOn_iff_convex.mp hc
  have hline : HasDerivAt (fun t : ℝ => x+t • (y-x)) (y-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y-x)).const_add x
  have hd:= (hf (x+(0:ℝ) • (y-x))).hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
  simp only [zero_smul,add_zero] at hd
  rw [← inner_gradient_left] at hd
  have hn : HasDerivAt (fun t : ℝ => ‖x+t • (y-x)‖^2) (2*⟪x,y-x⟫) 0 := by
    have hh:=hline.inner ℝ hline
    simpa only [real_inner_self_eq_norm_sq,zero_smul,add_zero,real_inner_comm,two_mul] using hh
  have hdq:=hd.sub (hn.const_mul (μ/2))
  have hq' : ConvexOn ℝ Set.univ (fun t : ℝ => q (x+t • (y-x))) := by
    simpa [Function.comp_def,AffineMap.lineMap_apply_module',add_comm] using hq.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hh:=hq'.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num : (0:ℝ)<1) hdq
  simp only [slope_def_field,q,zero_smul,add_zero,one_smul,add_sub_cancel,sub_zero,div_one] at hh
  rw [norm_sub_sq_real,inner_sub_right]
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm] at hh ⊢
  nlinarith

private theorem grad_mono {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hc : StrongConvexOn Set.univ μ f) (x y : EuclideanSpace ℝ (Fin n)) :
    μ*‖x-y‖^2 ≤ ⟪gradient f x-gradient f y,x-y⟫ := by
  have h1:=strong_first f μ hf hc x y
  have h2:=strong_first f μ hf hc y x
  rw [norm_sub_rev y x] at h1
  rw [show y-x=-(x-y) by abel,inner_neg_right] at h1
  rw [inner_sub_left]
  linarith

private theorem hessian_lower {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hc : StrongConvexOn Set.univ μ f) (x v : EuclideanSpace ℝ (Fin n)) :
    μ*‖v‖^2 ≤ hessQuad f x v := by
  let q : ℝ → ℝ := fun t => fderiv ℝ f (x+t • v) v
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd : HasDerivAt q (hessQuad f x v) 0 := by
    have hh:=(hf' (x+(0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
    simpa [q,hessQuad] using hh.clm_apply (hasDerivAt_const (0:ℝ) v)
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hm:=grad_mono f μ hf hc (x+t • v) x
  simp only [add_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,mul_pow,
    inner_smul_right,inner_sub_left,inner_gradient_left] at hm
  change μ*‖v‖^2 ≤ t⁻¹*(q (0+t)-q 0)
  simp only [q,zero_add,zero_smul,add_zero]
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ ht0).mpr
  exact (mul_le_mul_iff_left₀ ht0).mp (by nlinarith [hm])

private theorem hessian_upper {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hL0 : 0 ≤ L)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x v : EuclideanSpace ℝ (Fin n)) :
    hessQuad f x v ≤ L*‖v‖^2 := by
  have hd : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L := by
    apply norm_fderiv_le_of_lip' ℝ hL0
    apply Eventually.of_forall
    intro y
    have he : fderiv ℝ f y-fderiv ℝ f x=(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (gradient f y-gradient f x) := by
      rw [map_sub,toDual_gradient,toDual_gradient]
    rw [he,LinearIsometryEquiv.norm_map]
    exact hL y x
  have h1:=(fderiv ℝ (fderiv ℝ f) x v).le_opNorm v
  have h2:=(fderiv ℝ (fderiv ℝ f) x).le_opNorm v
  apply (le_abs_self (hessQuad f x v)).trans
  change |fderiv ℝ (fderiv ℝ f) x v v| ≤ _
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x v‖*‖v‖ := h1
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ L*‖v‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖v‖)]

private theorem smooth_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f) (hL0 : 0 ≤ L)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x d : EuclideanSpace ℝ (Fin n)) :
    f (x+d) ≤ f x+⟪gradient f x,d⟫+L/2*‖d‖^2 := by
  let q : ℝ → ℝ := fun t => f (x+t • d)-f x-t*⟪gradient f x,d⟫
  let B : ℝ → ℝ := fun t => L/2*‖d‖^2*t^2
  have hd (t : ℝ) : HasDerivAt q ⟪gradient f (x+t • d)-gradient f x,d⟫ t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh:=(hf (x+t • d)).hasFDerivAt.comp_hasDerivAt t hl
    rw [← inner_gradient_left] at hh
    convert! (hh.sub_const (f x)).sub ((hasDerivAt_id t).mul_const ⟪gradient f x,d⟫) using 1 <;> simp [q,inner_sub_left]
  have hB (t : ℝ) : HasDerivAt B (L*‖d‖^2*t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_mul (L/2*‖d‖^2) using 1 <;> dsimp only [B,id_eq] <;> ring
  have hh:=image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := (0:ℝ)) (b := 1) (fun t ht => (hd t).continuousAt.continuousWithinAt)
    (fun t ht => (hd t).hasDerivWithinAt) (B:=B) (B':=fun t => L*‖d‖^2*t)
    (by simp [q,B]) hB (by
      intro t ht
      have hb:=norm_inner_le_norm (𝕜 := ℝ) (gradient f (x+t • d)-gradient f x) d
      have hl:=hL (x+t • d) x
      simp only [add_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hl
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg d)]))
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  have hr:=(le_abs_self (q 1)).trans hh
  simp only [q,B,one_smul,one_pow,mul_one,one_mul] at hr
  linarith

private theorem linear_taylor {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : EuclideanSpace ℝ (Fin n) → Y) (M : ℝ) (hF : Differentiable ℝ F) (hM0 : 0 ≤ M)
    (hM : ∀ x y,‖fderiv ℝ F x-fderiv ℝ F y‖ ≤ M*‖x-y‖) (x d : EuclideanSpace ℝ (Fin n)) :
    ‖F (x+d)-F x-fderiv ℝ F x d‖ ≤ M/2*‖d‖^2 := by
  let q : ℝ → Y := fun t => F (x+t • d)-F x-t • fderiv ℝ F x d
  let B : ℝ → ℝ := fun t => M/2*‖d‖^2*t^2
  have hd (t : ℝ) : HasDerivAt q ((fderiv ℝ F (x+t • d)-fderiv ℝ F x) d) t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh:=(hF (x+t • d)).hasFDerivAt.comp_hasDerivAt t hl
    convert! (hh.sub_const (F x)).sub ((hasDerivAt_id t).smul_const (fderiv ℝ F x d)) using 1 <;> simp [q]
  have hB (t : ℝ) : HasDerivAt B (M*‖d‖^2*t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_mul (M/2*‖d‖^2) using 1 <;> dsimp only [B,id_eq] <;> ring
  have hh:=image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := (0:ℝ)) (b := 1) (fun t ht => (hd t).continuousAt.continuousWithinAt)
    (fun t ht => (hd t).hasDerivWithinAt) (B:=B) (B':=fun t => M*‖d‖^2*t)
    (by simp [q,B]) hB (by
      intro t ht
      have hb:=(fderiv ℝ F (x+t • d)-fderiv ℝ F x).le_opNorm d
      have hl:=hM (x+t • d) x
      simp only [add_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hl
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg d)]))
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa [q,B] using hh

private theorem scalar_taylor {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f)) (hM0 : 0 ≤ M)
    (hM : ∀ x y,‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ M*‖x-y‖)
    (x d : EuclideanSpace ℝ (Fin n)) :
    f (x+d) ≤ f x+fderiv ℝ f x d+1/2*hessQuad f x d+M/6*‖d‖^3 := by
  let q : ℝ → ℝ := fun t => f (x+t • d)-f x-t*fderiv ℝ f x d-t^2/2*hessQuad f x d
  let B : ℝ → ℝ := fun t => M/6*‖d‖^3*t^3
  have hd (t : ℝ) : HasDerivAt q ((fderiv ℝ f (x+t • d)-fderiv ℝ f x-fderiv ℝ (fderiv ℝ f) x (t • d)) d) t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh:=(hf (x+t • d)).hasFDerivAt.comp_hasDerivAt t hl
    convert! ((hh.sub_const (f x)).sub ((hasDerivAt_id t).mul_const (fderiv ℝ f x d))).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const (hessQuad f x d)) using 1 <;>
      simp only [q,hessQuad,Pi.sub_apply,id_eq,map_smul,sub_apply,smul_apply,smul_eq_mul] <;> ring
  have hB (t : ℝ) : HasDerivAt B (M/2*‖d‖^3*t^2) t := by
    convert! ((hasDerivAt_id t).pow 3).const_mul (M/6*‖d‖^3) using 1 <;> dsimp only [B,id_eq] <;> ring
  have hh:=image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := (0:ℝ)) (b := 1) (fun t ht => (hd t).continuousAt.continuousWithinAt)
    (fun t ht => (hd t).hasDerivWithinAt) (B:=B) (B':=fun t => M/2*‖d‖^3*t^2)
    (by simp [q,B]) hB (by
      intro t ht
      have hb:=(fderiv ℝ f (x+t • d)-fderiv ℝ f x-fderiv ℝ (fderiv ℝ f) x (t • d)).le_opNorm d
      have hl:=linear_taylor (fderiv ℝ f) M hf' hM0 hM x (t • d)
      simp only [norm_neg,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hl
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg d)]))
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  have hr:=(le_abs_self (q 1)).trans hh
  simp only [q,B,one_smul,one_pow,mul_one,one_mul,one_div] at hr
  linarith

private theorem step_basic {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f) (x : EuclideanSpace ℝ (Fin n))
    (hg : gradient f x ≠ 0) :
    0 < hessStep f x ∧ hessStep f x ≤ 1/μ ∧
      hessStep f x*hessQuad f x (gradient f x)=‖gradient f x‖^2 := by
  have hn : 0 < ‖gradient f x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hl:=hessian_lower f μ hf hf' hc x (gradient f x)
  have hd : 0 < hessQuad f x (gradient f x) := (mul_pos hμ hn).trans_le hl
  refine ⟨div_pos hn hd,?_,?_⟩
  · apply (div_le_div_iff₀ hd hμ).mpr
    nlinarith
  · exact div_mul_cancel₀ _ (ne_of_gt hd)

private theorem step_lower {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f) (hL0 : 0 < L)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x : EuclideanSpace ℝ (Fin n)) (hg : gradient f x ≠ 0) : 1/L ≤ hessStep f x := by
  have hn : 0 < ‖gradient f x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hd : 0 < hessQuad f x (gradient f x) :=
    (mul_pos hμ hn).trans_le (hessian_lower f μ hf hf' hc x (gradient f x))
  apply (div_le_div_iff₀ hL0 hd).mpr
  simpa only [one_mul,mul_comm] using hessian_upper f L hL0.le hL x (gradient f x)
private theorem ordinary_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖)
    (x : EuclideanSpace ℝ (Fin n)) :
    f (x - hessStep f x • gradient f x) ≤
      f x - (1 / 2) * hessStep f x * ‖gradient f x‖ ^ 2 *
        (1 - M * hessStep f x ^ 2 / 3 * ‖gradient f x‖) := by
  by_cases hg : gradient f x=0
  · simp [hg,hessStep,hessQuad]
  obtain ⟨ha0,haμ,haeq⟩:=step_basic f μ hf hf' hμ hconv x hg
  have hM0 : 0 ≤ M := by
    have hh:=hM (x+gradient f x) x
    simp only [add_sub_cancel_left] at hh
    have hn : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
    nlinarith [norm_nonneg (fderiv ℝ (fderiv ℝ f) (x+gradient f x)-fderiv ℝ (fderiv ℝ f) x)]
  have hh:=scalar_taylor f M hf hf' hM0 hM x (-(hessStep f x) • gradient f x)
  have hq : hessQuad f x (-(hessStep f x) • gradient f x)=hessStep f x^2*hessQuad f x (gradient f x) := by
    simp only [hessQuad,map_smul,smul_apply,smul_eq_mul]
    ring
  have hfval : fderiv ℝ f x (-(hessStep f x) • gradient f x)=-(hessStep f x)*‖gradient f x‖^2 := by
    rw [map_smul,smul_eq_mul,← inner_gradient_left,real_inner_self_eq_norm_sq]
  rw [hq,hfval] at hh
  simp only [neg_smul,← sub_eq_add_neg,norm_neg,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ha0,mul_pow] at hh
  have hqa : hessStep f x^2*hessQuad f x (gradient f x)=hessStep f x*‖gradient f x‖^2 := by
    nlinarith [congrArg (fun q => hessStep f x*q) haeq]
  rw [hqa] at hh
  nlinarith

private theorem damped_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L σ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hσ : 0 < σ) (hσL : σ ≤ μ / L)
    (x : EuclideanSpace ℝ (Fin n)) :
    f (x - (σ * hessStep f x) • gradient f x) ≤
      f x - σ * hessStep f x / 2 * ‖gradient f x‖ ^ 2 := by
  by_cases hg : gradient f x=0
  · simp [hg,hessStep,hessQuad]
  have hL0 : 0 < L := by
    by_contra hn
    have hh:=div_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hn)
    linarith
  obtain ⟨ha0,haμ,haeq⟩:=step_basic f μ hf hf' hμ hconv x hg
  have haL : L*(σ*hessStep f x) ≤ 1 := by
    have hh:=(le_div_iff₀ hL0).mp hσL
    have hh2:=(le_div_iff₀ hμ).mp haμ
    have hm:=mul_le_mul_of_nonneg_left hh ha0.le
    nlinarith
  have hsa : 0 < σ*hessStep f x := mul_pos hσ ha0
  have hh:=smooth_descent f L hf hL0.le hL x (-(σ*hessStep f x) • gradient f x)
  simp only [neg_smul,← sub_eq_add_neg,real_inner_smul_right,inner_neg_right,real_inner_self_eq_norm_sq,
    norm_neg,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hsa,mul_pow] at hh
  have hm:=mul_le_mul_of_nonneg_right haL (show 0 ≤ (σ*hessStep f x)*‖gradient f x‖^2 by positivity)
  nlinarith

private theorem gradient_lower {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f)
    (x xs : EuclideanSpace ℝ (Fin n)) : 2*μ*(f x-f xs) ≤ ‖gradient f x‖^2 := by
  have hh:=strong_first f μ hf hc x xs
  have hm:=mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*μ by positivity)
  have hq:=sq_nonneg ‖gradient f x+μ • (xs-x)‖
  rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_right] at hq
  nlinarith

private theorem gradient_upper {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f) (hL0 : 0 < L)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y,f xs ≤ f y) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x‖^2 ≤ 2*L*(f x-f xs) := by
  have hh:=smooth_descent f L hf hL0.le hL x (-(1/L) • gradient f x)
  simp only [neg_smul,← sub_eq_add_neg,inner_neg_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1/L),mul_pow] at hh
  have he : -(1/L*‖gradient f x‖^2)+L/2*((1/L)^2*‖gradient f x‖^2) = -‖gradient f x‖^2/(2*L) := by
    field_simp
    ring
  have hnext:=hmin (x-(1/L) • gradient f x)
  have hg : ‖gradient f x‖^2/(2*L) ≤ f x-f xs := by
    ring_nf at hh he hnext ⊢
    linarith
  have hh2:=(div_le_iff₀ (show 0 < 2*L by positivity)).mp hg
  nlinarith

private theorem stationary_min {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (hf : Differentiable ℝ f) (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y,f xs ≤ f y)
    (x : EuclideanSpace ℝ (Fin n)) (hg : gradient f x=0) : f x=f xs := by
  have hh:=strong_first f μ hf hc x xs
  rw [hg,inner_zero_left] at hh
  have hp:=mul_nonneg (show 0 ≤ μ/2 by positivity) (sq_nonneg ‖xs-x‖)
  exact le_antisymm (by linarith) (hmin x)

private theorem constants_valid {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L M : ℝ)
    (hf : Differentiable ℝ f) (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hM : ∀ x y,‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ M*‖x-y‖)
    (u : EuclideanSpace ℝ (Fin n)) (hu : gradient f u ≠ 0) : μ ≤ L ∧ 0 < L ∧ 0 ≤ M := by
  have hn : 0 < ‖gradient f u‖ := norm_pos_iff.mpr hu
  have hgm:=grad_mono f μ hf hc (u+gradient f u) u
  have hl:=hL (u+gradient f u) u
  simp only [add_sub_cancel_left] at hgm hl
  have hb:=real_inner_le_norm (gradient f (u+gradient f u)-gradient f u) (gradient f u)
  have hp:=mul_le_mul_of_nonneg_right hl hn.le
  have hμL : μ ≤ L := by nlinarith [sq_pos_of_pos hn]
  refine ⟨hμL,hμ.trans_le hμL,?_⟩
  have hm:=hM (u+gradient f u) u
  simp only [add_sub_cancel_left] at hm
  nlinarith [norm_nonneg (fderiv ℝ (fderiv ℝ f) (u+gradient f u)-fderiv ℝ (fderiv ℝ f) u)]

private theorem decrease_product {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L δ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f) (hL0 : 0 < L) (hδ : 0 ≤ δ)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x xs : EuclideanSpace ℝ (Fin n)) (hg : gradient f x ≠ 0) :
    μ*δ/L*(f x-f xs) ≤ 1/2*hessStep f x*‖gradient f x‖^2*δ := by
  have hp:=gradient_lower f μ hf hμ hc x xs
  have ha:=step_lower f μ L hf hf' hμ hc hL0 hL x hg
  calc
    μ*δ/L*(f x-f xs) = (δ/2)*((1/L)*(2*μ*(f x-f xs))) := by ring
    _ ≤ (δ/2)*((1/L)*‖gradient f x‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ ≤ (δ/2)*(hessStep f x*‖gradient f x‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha (sq_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem ordinary_contract {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L M δ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f) (hL0 : 0 < L)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hM : ∀ x y,‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ M*‖x-y‖)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y,f xs ≤ f y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : EuclideanSpace ℝ (Fin n))
    (hbudget : M*‖gradient f x‖ ≤ 3*μ^2*(1-δ)) :
    f (x-hessStep f x • gradient f x)-f xs ≤ (f x-f xs)*(1-μ*δ/L) := by
  by_cases hg : gradient f x=0
  · have he:=stationary_min f μ hf hμ hc xs hmin x hg
    simp [hg,hessStep,hessQuad,he]
  obtain ⟨ha0,haμ,haeq⟩:=step_basic f μ hf hf' hμ hc x hg
  have hαμ:=(le_div_iff₀ hμ).mp haμ
  have hasq:=pow_le_pow_left₀ (mul_nonneg ha0.le hμ.le) hαμ 2
  simp only [mul_pow,one_pow] at hasq
  have hm1:=mul_le_mul_of_nonneg_left hbudget (sq_nonneg (hessStep f x))
  have hm2:=mul_le_mul_of_nonneg_right hasq (show 0 ≤ 3*(1-δ) by linarith)
  have hfactor : δ ≤ 1-M*hessStep f x^2/3*‖gradient f x‖ := by nlinarith
  have hh:=ordinary_descent f μ M hf hf' hμ hc hM x
  have hd:=decrease_product f μ L δ hf hf' hμ hc hL0 hδ.le hL x xs hg
  have hp:=mul_le_mul_of_nonneg_left hfactor (show 0 ≤ (1/2)*hessStep f x*‖gradient f x‖^2 by positivity)
  nlinarith

private theorem damped_contract {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L σ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hc : StrongConvexOn Set.univ μ f) (hL0 : 0 < L)
    (hL : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y,f xs ≤ f y)
    (hσ : 0 < σ) (hσL : σ ≤ μ/L) (x : EuclideanSpace ℝ (Fin n)) :
    f (x-(σ*hessStep f x) • gradient f x)-f xs ≤ (f x-f xs)*(1-μ*σ/L) := by
  by_cases hg : gradient f x=0
  · have he:=stationary_min f μ hf hμ hc xs hmin x hg
    simp [hg,hessStep,hessQuad,he]
  have hh:=damped_descent f μ L σ hf hf' hμ hc hL hσ hσL x
  have hd:=decrease_product f μ L σ hf hf' hμ hc hL0 hσ.le hL x xs hg
  nlinarith
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L M : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖)
    (hmin : ∀ y : EuclideanSpace ℝ (Fin n), f xstar ≤ f y) :
    (∀ (δ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)), 0 < δ →
        M * Real.sqrt (2 * L * (f x₀ - f xstar)) ≤ 3 * μ ^ 2 * (1 - δ) →
        ∀ j : ℕ, f (hessIter f x₀ j) - f xstar ≤ (f x₀ - f xstar) * (1 - μ * δ / L) ^ j) ∧
    (∀ σ : ℝ, 0 < σ → σ ≤ μ / L → ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ),
        f (dampedHessIter f σ x₀ j) - f xstar ≤ (f x₀ - f xstar) * (1 - μ * σ / L) ^ j) := by
  by_cases hzero : ∀ u,gradient f u=0
  · have he (u) : f u=f xstar := stationary_min f μ hf hμ hconv xstar hmin u (hzero u)
    simp only [he,sub_self,zero_mul,le_refl,implies_true,forall_const,and_self]
  push_neg at hzero
  obtain ⟨u,hu⟩:=hzero
  obtain ⟨hμL,hL0,hM0⟩:=constants_valid f μ L M hf hμ hconv hL hM u hu
  constructor
  · intro δ x₀ hδ hbudget j
    have hδ1 : δ ≤ 1 := by
      by_contra hn
      have hn' : 1 < δ := lt_of_not_ge hn
      have hp:=mul_neg_of_pos_of_neg (show 0 < 3*μ^2 by positivity) (show 1-δ < 0 by linarith)
      have hnon:=mul_nonneg hM0 (Real.sqrt_nonneg (2*L*(f x₀-f xstar)))
      linarith
    let ρ:=1-μ*δ/L
    have hρ0 : 0 ≤ ρ := by
      have hh : μ*δ ≤ L := (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 hμ.le : μ*δ ≤ μ).trans hμL
      have hh2 : μ*δ/L ≤ 1 := (div_le_iff₀ hL0).mpr (by simpa using hh)
      dsimp [ρ]
      linarith
    have hρ1 : ρ ≤ 1 := by
      have hh : 0 ≤ μ*δ/L := by positivity
      dsimp [ρ]
      linarith
    have hgap0 : 0 ≤ f x₀-f xstar := sub_nonneg.mpr (hmin x₀)
    have hstep (x : EuclideanSpace ℝ (Fin n)) (hx : f x-f xstar ≤ f x₀-f xstar) :
        f (x-hessStep f x • gradient f x)-f xstar ≤ (f x-f xstar)*ρ := by
      have hsq:= (gradient_upper f L hf hL0 hL xstar hmin x).trans
        (mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*L by positivity))
      have hn : ‖gradient f x‖ ≤ Real.sqrt (2*L*(f x₀-f xstar)) := by
        simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hsq
      have hb:=(mul_le_mul_of_nonneg_left hn hM0).trans hbudget
      exact ordinary_contract f μ L M δ hf hf' hμ hconv hL0 hL hM xstar hmin hδ hδ1 x hb
    have hind (k : ℕ) : f (hessIter f x₀ k)-f xstar ≤ (f x₀-f xstar)*ρ^k ∧
        f (hessIter f x₀ k)-f xstar ≤ f x₀-f xstar := by
      induction k with
      | zero => simp [hessIter]
      | succ k ih =>
        have hh:=hstep (hessIter f x₀ k) ih.2
        constructor
        · calc
            _ ≤ (f (hessIter f x₀ k)-f xstar)*ρ := hh
            _ ≤ ((f x₀-f xstar)*ρ^k)*ρ := mul_le_mul_of_nonneg_right ih.1 hρ0
            _ = _ := by rw [pow_succ];ring
        · have hm:=mul_le_mul_of_nonneg_left hρ1 (sub_nonneg.mpr (hmin (hessIter f x₀ k)))
          simp only [mul_one] at hm
          exact hh.trans (hm.trans ih.2)
    exact (hind j).1
  · intro σ hσ hσL x₀ j
    have hσ1 : σ ≤ 1 := hσL.trans ((div_le_one hL0).mpr hμL)
    have hρ0 : 0 ≤ 1-μ*σ/L := by
      have hh : μ*σ ≤ L := (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hσ1 hμ.le : μ*σ ≤ μ).trans hμL
      have hh2 : μ*σ/L ≤ 1 := (div_le_iff₀ hL0).mpr (by simpa using hh)
      linarith
    induction j with
    | zero => simp [dampedHessIter]
    | succ j ih =>
      have hh:=damped_contract f μ L σ hf hf' hμ hconv hL0 hL xstar hmin hσ hσL (dampedHessIter f σ x₀ j)
      calc
        _ ≤ (f (dampedHessIter f σ x₀ j)-f xstar)*(1-μ*σ/L) := hh
        _ ≤ ((f x₀-f xstar)*(1-μ*σ/L)^j)*(1-μ*σ/L) := mul_le_mul_of_nonneg_right ih hρ0
        _ = _ := by rw [pow_succ];ring
