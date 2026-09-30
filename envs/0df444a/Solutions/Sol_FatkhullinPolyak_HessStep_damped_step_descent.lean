-- Prove2me | solution 1 for FatkhullinPolyak.HessStep.damped_step_descent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:42:42.660444+00:00
-- url     : https://prove2.me/submissions/a1a32a52-97fc-4d85-85a7-e6572c1a3929

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
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L σ : ℝ)
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
