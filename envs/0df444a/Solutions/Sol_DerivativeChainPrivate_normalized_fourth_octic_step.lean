-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fourth_octic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T16:01:07.154209+00:00
-- url     : https://prove2.me/submissions/393d7698-9563-4d2f-a5c4-1821ce1bd76f

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


section
-- Source module: VerifiedCube

open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem derivative_real_supporting_parent (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (w : ℂ) (hw : p.derivative.eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by
  have hd : p.derivative ≠ 0 := by
    intro h
    have hconst := Polynomial.derivative_eq_zero.mp h
    have hzero : p.natDegree = 0 := by simpa [hconst]
    omega
  have hwset : w ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hw⟩
  have hwconv := p.rootSet_derivative_subset_convexHull_rootSet
    (Polynomial.natDegree_pos_iff_degree_pos.mp hp) hwset
  by_contra h
  push Not at h
  have hlinear : IsLinearMap ℝ (fun z : ℂ => z.re) := by
    constructor
    · intro a b; simp
    · intro a b; simp
  have hsubset : p.rootSet ℂ ⊆ {z | z.re < w.re} := by
    intro z hz
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hz
    exact h z hz.2
  have hbad := (convexHull_min hsubset (convex_halfSpace_lt hlinear w.re)) hwconv
  exact (lt_irrefl w.re) hbad



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_graph_southeast_impossible
    (α₀ α₁ b₀ b₁ A₀ A₁ B₀ B₁ K R I x y r v : ℝ)
    (hα₁ : 0 < α₁) (hα : α₁ < α₀)
    (hx : 0 < x) (hv : 0 < v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hC₀ : (3 * A₀ - B₀) / 2 ≤ K) (hC₁ : 0 ≤ (3 * A₁ - B₁) / 2)
    (hgap : K < b₀ - b₁)
    (hR₀ : R / x = α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀)
    (hI₀ : I / y = α₀ * (3 * x ^ 2 - y ^ 2) - b₀ + B₀)
    (hR₁ : R / r = α₁ * (r ^ 2 - 3 * v ^ 2) - b₁ + A₁)
    (hI₁ : I / v = α₁ * (3 * r ^ 2 - v ^ 2) - b₁ + B₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  have himag := div_le_div_of_nonneg_left hI hv hvy
  rw [hR₀, hR₁] at hreal
  rw [hI₀, hI₁] at himag
  have hsq : v ^ 2 ≤ y ^ 2 := by nlinarith only [hv, hvy]
  have hterm₀ := mul_nonneg (sub_pos.mpr hα).le (sq_nonneg y)
  have hterm₁ := mul_nonneg hα₁.le (sub_nonneg.mpr hsq)
  nlinarith only [hreal, himag, hterm₀, hterm₁, hC₀, hC₁, hgap]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



theorem rational_inverse_parts (β z : ℂ) (α b d c : ℝ)
    (hz : z ≠ 0) (hpole : z ^ 2 - (c : ℂ) ≠ 0)
    (hβ : β / z = (α : ℂ) * z ^ 2 - (b : ℂ) + (d : ℂ) / (z ^ 2 - (c : ℂ))) :
    let U := z.re ^ 2 + z.im ^ 2
    let D := ‖z ^ 2 - (c : ℂ)‖ ^ 2
    β.re = z.re * (α * (z.re ^ 2 - 3 * z.im ^ 2) - b + d * (U - c) / D) ∧
      β.im = z.im * (α * (3 * z.re ^ 2 - z.im ^ 2) - b - d * (U + c) / D) ∧
      (β / z).im = 2 * z.re * z.im * (α - d / D) ∧
      D = (U - c) ^ 2 + 4 * c * z.im ^ 2 := by
  have hD : Complex.normSq (z ^ 2 - (c : ℂ)) ≠ 0 := by
    simpa only [← Complex.sq_norm, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hpole
  have heq := (div_eq_iff hz).mp hβ
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two, ← Complex.sq_norm]
    field_simp [hD]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two, ← Complex.sq_norm]
    field_simp [hD]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [hβ]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re,
      Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, ← Complex.sq_norm]
    field_simp [hD]
    ring
  · rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    ring

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_graph_coordinate_parts (β z e : ℂ) (α b : ℝ) (hz : z ≠ 0)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+e/z) :
    β.re = z.re * (α*(z.re^2-3*z.im^2)-b)+e.re ∧
      β.im = z.im * (α*(3*z.re^2-z.im^2)-b)+e.im ∧
      (β/z).im = 2*α*z.re*z.im+(e/z).im := by
  have hgraph : β = (α : ℂ)*z^3-(b : ℂ)*z+e := by
    calc
      _ = ((α : ℂ)*z^2-(b : ℂ)+e/z)*z := (div_eq_iff hz).mp hβ
      _ = _ := by rw [add_mul,sub_mul,div_mul_cancel₀ _ hz]; ring
  refine ⟨?_,?_,?_⟩
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_im,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hβ]
    simp only [pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im]
    ring

theorem quotient_imaginary_identity (z e : ℂ) (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    (e/z).im/(2*z.re*z.im) = (e.im/z.im-e.re/z.re)/(2*(z.re^2+z.im^2)) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hD : Complex.normSq z ≠ 0 := by
    rw [← Complex.sq_norm]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [Complex.div_im]
  simp only [Complex.normSq_apply]
  have hsum : z.re*z.re+z.im*z.im ≠ 0 := by simpa only [Complex.normSq_apply] using hD
  field_simp

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



end


section
-- Source module: SexticPick


set_option autoImplicit false
open Set
namespace DerivativeChainPrivate











theorem real_quadratic_nonnegative_discriminant_root_im (A B C : ℝ)
    (hC : C ≠ 0) (hD : 0 ≤ B^2-4*A*C) (z : ℂ)
    (hroot : (A : ℂ)*z^2+(B : ℂ)*z+(C : ℂ)=0) : z.im = 0 := by
  by_contra hy
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
    zero_mul,mul_zero,zero_add,add_zero,sub_zero] at hre him
  have hm : z.im*(2*A*z.re+B)=0 := by nlinarith only [him]
  have hl := (mul_eq_zero.mp hm).resolve_left hy
  have hA : A ≠ 0 := by
    intro ha
    rw [ha] at hl hre
    have hb : B = 0 := by simpa using hl
    apply hC
    simpa [hb] using hre
  have heq : B^2-4*A*C = -4*A^2*z.im^2 := by
    linear_combination (2*A*z.re+B)*hl-4*A*hre
  have hpos := mul_pos (sq_pos_of_ne_zero hA) (sq_pos_of_ne_zero hy)
  nlinarith only [heq,hD,hpos]





end DerivativeChainPrivate

end


section
-- Source module: CauchyRootKernel


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_root_kernel_bound (z : ℂ) (hx : 5/2 ≤ z.re^2) (t : ℝ)
    (ht : t ∈ Icc (-1/4:ℝ) (3/2)) :
    z^2-(t:ℂ) ≠ 0 ∧ ‖(z^2-(t:ℂ))⁻¹‖ ≤ (z.re^2-3/2)⁻¹ := by
  have htabs : |t| ≤ 3/2 := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  have hn : z.re^2-3/2 ≤ ‖z^2-(t:ℂ)‖ := by
    have htri := norm_sub_norm_le (z^2) (t:ℂ)
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs] at htri
    have hsq : z.re^2 ≤ ‖z‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      nlinarith [sq_nonneg z.im]
    linarith
  have hp : 0 < z.re^2-3/2 := by linarith
  constructor
  · exact norm_pos_iff.mp (lt_of_lt_of_le hp hn)
  · rw [norm_inv]
    exact inv_anti₀ hp hn





end DerivativeChainPrivate

end


section
-- Source module: FastBranchComparison


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fast_graph_northeast_impossible
    (α₀ α₁ b₀ b₁ A₁ B₀ B₁ Xmin K R I x y r v : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxr : x ≤ r) (hyv : y ≤ v)
    (hR : 0 ≤ R) (hI : 0 ≤ I) (hX : Xmin ≤ x^2)
    (hα₀ : 0 ≤ α₀) (hα₁ : 0 ≤ α₁) (hα : 3*α₀ < 8*α₁/3)
    (hB₀ : B₀ ≤ 0) (hcorrection : -K ≤ B₁-A₁/3)
    (hgap : 2*b₁/3-b₀+K < (8*α₁/3-3*α₀)*Xmin)
    (hI₀ : I/y = α₀*(3*x^2-y^2)-b₀+B₀)
    (hR₁ : R/r = α₁*(r^2-3*v^2)-b₁+A₁)
    (hI₁ : I/v = α₁*(3*r^2-v^2)-b₁+B₁) : False := by
  have hr : 0 < r := lt_of_lt_of_le hx hxr
  have hv : 0 < v := lt_of_lt_of_le hy hyv
  have hcmp := div_le_div_of_nonneg_left hI hy hyv
  rw [hI₀,hI₁] at hcmp
  have hrr : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hmul := mul_le_mul_of_nonneg_left hrr hα₁
  have hyterm := mul_nonneg hα₀ (sq_nonneg y)
  have hreal : 0 ≤ α₁*(r^2-3*v^2)-b₁+A₁ := by rw [← hR₁]; positivity
  have hxmin := mul_le_mul_of_nonneg_left hX (show 0 ≤ 8*α₁/3-3*α₀ by linarith)
  nlinarith only [hcmp,hmul,hyterm,hreal,hxmin,hgap,hB₀,hcorrection]

end DerivativeChainPrivate

namespace DerivativeChainPrivate

theorem cubic_graph_positive_phase_of_corrections (β z e : ℂ) (α b M : ℝ)
    (hx : 0 < z.re) (hy : 0 < z.im) (hX : 5/2 ≤ z.re^2)
    (hM : 0 ≤ M) (hα : M < α)
    (hA : e.re/z.re ≤ M) (hB : -4*M ≤ e.im/z.im)
    (hgraph : β/z = (α:ℂ)*z^2-(b:ℂ)+e/z) : 0 < (β/z).im := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hxy : 0 < 2*z.re*z.im := by positivity
  have hU : 5/2 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < 2*(z.re^2+z.im^2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hU hM
  have hcorr : -M ≤ (e.im/z.im-e.re/z.re)/(2*(z.re^2+z.im^2)) := by
    apply (le_div_iff₀ hUp).mpr
    linarith
  have hi := (cubic_graph_coordinate_parts β z e α b hz hgraph).2.2
  have hdiv : (β/z).im/(2*z.re*z.im) = α+(e/z).im/(2*z.re*z.im) := by
    rw [hi]; field_simp
  rw [quotient_imaginary_identity z e hx.ne' hy.ne'] at hdiv
  have hp : 0 < (β/z).im/(2*z.re*z.im) := by linarith
  exact (div_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1

end DerivativeChainPrivate

namespace DerivativeChainPrivate



end DerivativeChainPrivate

namespace DerivativeChainPrivate

theorem inverse_graph_large_slope_southeast_impossible
    (R x y r v α₀ α₁ b₀ b₁ A₀ A₁ W K₀ K₁ : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hv : 0 ≤ v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hW : W ≤ x^2-3*y^2) (hα₁ : 0 ≤ α₁) (hα : α₀ < α₁)
    (hA₀ : A₀ ≤ K₀) (hA₁ : K₁ ≤ A₁)
    (hgap : b₁-b₀+K₀-K₁ < (α₁-α₀)*W)
    (hR₀ : R/x = α₀*(x^2-3*y^2)-b₀+A₀)
    (hR₁ : R/r = α₁*(r^2-3*v^2)-b₁+A₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  rw [hR₀,hR₁] at hreal
  have hsqx : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hsqy : v^2 ≤ y^2 := by nlinarith only [hv,hvy]
  have hdiff : 0 ≤ (r^2-3*v^2)-(x^2-3*y^2) := by linarith only [hsqx,hsqy]
  have hmul := mul_nonneg hα₁ hdiff
  have hprod := mul_le_mul_of_nonneg_left hW (sub_nonneg.mpr hα.le)
  nlinarith only [hreal,hmul,hprod,hgap,hA₀,hA₁]

end DerivativeChainPrivate

end


section
-- Source module: SepticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators















theorem norm_real_power_sum_le {n : ℕ} (c : Fin n → ℝ) (u : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    ‖∑ i : Fin n, (c i:ℂ)*u^i.val‖ ≤ ∑ i : Fin n, |c i| *R^i.val := by
  calc
    _ ≤ ∑ i : Fin n, ‖(c i:ℂ)*u^i.val‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr

theorem septic_sqrt_poly_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    ‖septicSqrtPoly u-1‖ ≤ 1/5 := by
  have hs := norm_real_power_sum_le septicSqrtCoeffs u (4/9) (by norm_num) hu
  calc
    _ = ‖u‖*‖∑ i : Fin 7, (septicSqrtCoeffs i:ℂ)*u^i.val‖ := by simp [septicSqrtPoly,norm_mul]
    _ ≤ (4/9)*(∑ i : Fin 7, |septicSqrtCoeffs i| *(4/9:ℝ)^i.val) :=
      mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _ ≤ 1/5 := by norm_num [septicSqrtCoeffs,Fin.sum_univ_succ]

theorem septic_sqrt_residual_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    ‖septicSqrtResidual u‖ ≤ 1/5000 := by
  apply (norm_real_power_sum_le septicResidualCoeffs u (4/9) (by norm_num) hu).trans
  norm_num [septicResidualCoeffs,Fin.sum_univ_succ]

theorem septic_sqrt_radicand_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    ‖septicSqrtRadicand u-1‖ ≤ 1/2 := by
  have he : septicSqrtRadicand u-1 = -(11/18:ℂ)*u+(121/432:ℂ)*u^2 := by
    dsimp [septicSqrtRadicand]; ring
  rw [he]
  calc
    _ ≤ ‖-(11/18:ℂ)*u‖+‖(121/432:ℂ)*u^2‖ := norm_add_le _ _
    _ = (11/18:ℝ)*‖u‖+(121/432:ℝ)*‖u‖^2 := by norm_num [norm_mul,norm_pow]
    _ ≤ (11/18:ℝ)*(4/9)+(121/432:ℝ)*(4/9)^2 := by gcongr
    _ ≤ 1/2 := by norm_num

theorem septic_sqrt_slit (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    septicSqrtRadicand u ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hn := septic_sqrt_radicand_bound u hu
  have hr := Complex.re_le_norm (1-septicSqrtRadicand u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  linarith

theorem septic_sqrt_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    Complex.sqrt (septicSqrtRadicand u)+septicSqrtPoly u ≠ 0 ∧
      ‖(Complex.sqrt (septicSqrtRadicand u)+septicSqrtPoly u)⁻¹‖ ≤ 2 := by
  have hs : 0 ≤ (Complex.sqrt (septicSqrtRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp := septic_sqrt_poly_bound u hu
  have hr := Complex.re_le_norm (1-septicSqrtPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd := Complex.re_le_norm (Complex.sqrt (septicSqrtRadicand u)+septicSqrtPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/2:ℝ) ≤ ‖Complex.sqrt (septicSqrtRadicand u)+septicSqrtPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

end DerivativeChainPrivate

end


section
-- Source module: SepticTail


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem septic_tail_norm (w : ℂ) (hw : ‖w‖ ≤ 2/3) : ‖septicTail w‖ ≤ 1/1000000 := by
  have hu : ‖w^2‖ ≤ 4/9 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0 < (3*Real.sqrt 3/55:ℝ) := by positivity
  have hku : (3*Real.sqrt 3/55:ℝ) ≤ 19/200 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg 3
    nlinarith
  have hf : ‖1-(11/6:ℂ)*w^2‖ ≤ 49/27 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖(11/6:ℂ)*w^2‖ := norm_sub_le _ _
      _ = 1+(11/6:ℝ)*‖w^2‖ := by norm_num [norm_mul]
      _ ≤ 49/27 := by linarith
  have ht := septic_sqrt_residual_bound (w^2) hu
  have hd := (septic_sqrt_denominator_bound (w^2) hu).2
  calc
    _ = (3*Real.sqrt 3/55:ℝ)*‖w‖^13*‖1-(11/6:ℂ)*w^2‖*‖septicSqrtResidual (w^2)‖*
        ‖(Complex.sqrt (septicSqrtRadicand (w^2))+septicSqrtPoly (w^2))⁻¹‖ := by
      simp only [septicTail,div_eq_mul_inv,norm_mul,norm_neg,norm_pow,Complex.norm_real,
        Real.norm_eq_abs]
      norm_num [abs_of_nonneg (Real.sqrt_nonneg 3)]
    _ ≤ (19/200:ℝ)*(2/3)^13*(49/27)*(1/5000)*2 := by gcongr
    _ ≤ 1/1000000 := by norm_num

theorem septic_tail_differentiableAt (w : ℂ) (hw : ‖w‖ ≤ 2/3) :
    DifferentiableAt ℂ septicTail w := by
  have hu : ‖w^2‖ ≤ 4/9 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => septicSqrtRadicand (v^2)) w := by
    unfold septicSqrtRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (septicSqrtRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (septic_sqrt_slit (w^2) hu)).comp w hh
  have hp : DifferentiableAt ℂ (fun v : ℂ => septicSqrtPoly (v^2)) w := by
    unfold septicSqrtPoly
    fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => septicSqrtResidual (v^2)) w := by
    unfold septicSqrtResidual
    fun_prop
  have hd := (septic_sqrt_denominator_bound (w^2) hu).1
  unfold septicTail
  fun_prop

theorem septic_tail_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 3/10) :
    ‖deriv septicTail w‖ ≤ 1/50000 := by
  have hw' : ‖w‖ ≤ 11/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/10:ℝ), ‖u‖ ≤ 2/3 := by
    intro u hu
    have hd : ‖u-w‖ < 1/10 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ septicTail (Metric.ball w (1/10:ℝ)) := by
    intro u hu
    exact (septic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo septicTail (Metric.ball w (1/10:ℝ))
      (Metric.closedBall (septicTail w) (1/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := septic_tail_norm u (hball u hu)
    have h2 := septic_tail_norm w (by linarith)
    have hn := norm_sub_le (septicTail u) (septicTail w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/10)
  norm_num at hh
  exact hh

end DerivativeChainPrivate

end


section
-- Source module: SepticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators





theorem septic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt septicPolynomialError
      (-((3*Real.sqrt 3/55:ℝ):ℂ)*(∑ i : Fin 6,
        (septicErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2))) w := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (septicErrorCoeffs i:ℂ)

theorem septic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 3/10) :
    ‖deriv septicPolynomialError w‖ ≤ 29/2000 := by
  have hk : 0 < (3*Real.sqrt 3/55:ℝ) := by positivity
  have hku : (3*Real.sqrt 3/55:ℝ) ≤ 19/200 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg 3
    nlinarith
  rw [(septic_polynomial_error_hasDerivAt w).deriv]
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have hsum : ‖∑ i : Fin 6, (septicErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 6, |septicErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(3/10:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _ ≤ (19/200:ℝ)*(∑ i : Fin 6, |septicErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(3/10:ℝ)^(i.val+1)) :=
      mul_le_mul hku hsum (norm_nonneg _) (by norm_num)
    _ ≤ 29/2000 := by norm_num [septicErrorCoeffs,Fin.sum_univ_succ]

theorem septic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2 ≤ 3/10) :
    DifferentiableAt ℂ septicError w := by
  have hn : ‖w‖ ≤ 2/3 := by nlinarith [norm_nonneg w]
  exact (septic_polynomial_error_hasDerivAt w).differentiableAt.add (septic_tail_differentiableAt w hn)

theorem septic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 3/10) :
    ‖deriv septicError w‖ ≤ 3/200 := by
  have hn : ‖w‖ ≤ 2/3 := by nlinarith [norm_nonneg w]
  have hp := septic_polynomial_error_deriv_bound w hw
  have ht := septic_tail_deriv_bound w hw
  have hd : deriv septicError w = deriv septicPolynomialError w+deriv septicTail w := by
    exact deriv_add (septic_polynomial_error_hasDerivAt w).differentiableAt (septic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv septicPolynomialError w) (deriv septicTail w)
  linarith

end DerivativeChainPrivate

end


section
-- Source module: SepticAxes


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem septic_radicand_real (x : ℝ) : septicSqrtRadicand (x:ℂ) =
    ((1-(11/18)*x+(121/432)*x^2:ℝ):ℂ) := by
  simp [septicSqrtRadicand]

theorem septic_poly_real (x : ℝ) : septicSqrtPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 7, septicSqrtCoeffs i*x^i.val):ℝ):ℂ) := by
  simp [septicSqrtPoly]

theorem septic_residual_real (x : ℝ) : septicSqrtResidual (x:ℂ) =
    ((∑ i : Fin 7, septicResidualCoeffs i*x^i.val : ℝ):ℂ) := by
  simp [septicSqrtResidual]

theorem septic_sqrt_real (x : ℝ) : Complex.sqrt (septicSqrtRadicand (x:ℂ)) =
    ((Real.sqrt (1-(11/18)*x+(121/432)*x^2):ℝ):ℂ) := by
  have hp : 0 ≤ 1-(11/18:ℝ)*x+(121/432:ℝ)*x^2 := by nlinarith [sq_nonneg (x-12/11)]
  rw [septic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp),Complex.ofReal_re]

theorem septic_tail_real_axis (x : ℝ) : (septicTail (x:ℂ)).im = 0 := by
  unfold septicTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [septic_sqrt_real,septic_poly_real,septic_residual_real]
  rw [← Complex.ofReal_pow]
  rw [show (11/6:ℂ)=((11/6:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,Complex.ofReal_im]

theorem septic_tail_imaginary_axis (x : ℝ) : (septicTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold septicTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [septic_sqrt_real,septic_poly_real,septic_residual_real]
  have he : (Complex.I*(x:ℂ))^13 = Complex.I*((x^13:ℝ):ℂ) := by norm_num [mul_pow,Complex.I_pow_eq_pow_mod]
  rw [he]
  rw [show (11/6:ℂ)=((11/6:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div]
  simp only [Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,
    mul_one,one_mul,neg_zero,zero_div]

theorem septic_error_axes (x : ℝ) :
    (septicError (x:ℂ)).im = 0 ∧ (septicError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [septicError,Complex.add_im,septic_tail_real_axis,add_zero]
    norm_num [septicPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [septicError,Complex.add_re,septic_tail_imaginary_axis,add_zero]
    norm_num [septicPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]

end DerivativeChainPrivate

end


section
-- Source module: SepticCoordinates


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem septic_error_coordinate_bounds (w : ℂ) (hw : ‖w‖^2 ≤ 3/10) :
    |(septicError w).re| ≤ (3/200)*|w.re| ∧
      |(septicError w).im| ≤ (3/200)*|w.im| := by
  let S := Metric.closedBall (0:ℂ) ‖w‖
  have hs (v : ℂ) (hv : v ∈ S) : ‖v‖^2 ≤ 3/10 := by
    have hn : ‖v‖ ≤ ‖w‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hw
  have hd : ∀ v ∈ S, DifferentiableAt ℂ septicError v := fun v hv => septic_error_differentiableAt v (hs v hv)
  have hb : ∀ v ∈ S, ‖deriv septicError v‖ ≤ 3/200 := fun v hv => septic_error_deriv_bound v (hs v hv)
  have hc : Convex ℝ S := convex_closedBall (0:ℂ) ‖w‖
  have hwm : w ∈ S := by simp [S]
  have hxr : (w.re:ℂ) ∈ S := by
    simpa only [S,Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using Complex.abs_re_le_norm w
  have hyi : Complex.I*(w.im:ℂ) ∈ S := by
    simpa only [S,Metric.mem_closedBall,dist_zero_right,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs] using Complex.abs_im_le_norm w
  constructor
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hyi hwm
    have he : w-Complex.I*(w.im:ℂ) = (w.re:ℂ) := by apply Complex.ext <;> simp
    rw [he,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_re_le_norm (septicError w-septicError (Complex.I*(w.im:ℂ)))
    rw [Complex.sub_re,(septic_error_axes w.im).2,sub_zero] at hp
    exact hp.trans hh
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hxr hwm
    have he : w-(w.re:ℂ) = Complex.I*(w.im:ℂ) := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_im_le_norm (septicError w-septicError (w.re:ℂ))
    rw [Complex.sub_im,(septic_error_axes w.re).1,sub_zero] at hp
    exact hp.trans hh




theorem septic_leading_error_bounds : (29/1000:ℝ) < septicLeadingError ∧ septicLeadingError < 3/100 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg 3
  dsimp only [septicLeadingError]
  constructor <;> nlinarith

theorem septic_remainder_coordinate_bounds (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im)
    (hX : 10/3 ≤ z.re^2) :
    0 < (septicRemainder z).re/z.re ∧ (septicRemainder z).re/z.re ≤ 27/2000 ∧
      -(27/2000) ≤ (septicRemainder z).im/z.im ∧ (septicRemainder z).im/z.im < 0 ∧
      0 < (3*((septicRemainder z).re/z.re)-(septicRemainder z).im/z.im)/2 ∧
      (4 ≤ z.re^2 → (3*((septicRemainder z).re/z.re)-(septicRemainder z).im/z.im)/2 ≤ 9/400) ∧
      (septicRemainder z).re/z.re ≤ (9/200)/(z.re^2+z.im^2) ∧
      -(9/200)/(z.re^2+z.im^2) ≤ (septicRemainder z).im/z.im := by
  let U := z.re^2+z.im^2
  have hU : 10/3 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith
  have hUn : Complex.normSq z = U := by simp [U,Complex.normSq_apply,pow_two]
  have hn : ‖z⁻¹‖^2 ≤ 3/10 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,hUn]
    exact (inv_le_comm₀ hUp (by norm_num)).mpr (by norm_num; exact hU)
  obtain ⟨hr,hi⟩ := septic_error_coordinate_bounds z⁻¹ hn
  have hwr : (z⁻¹).re = z.re/U := by rw [Complex.inv_re,hUn]
  have hwi : (z⁻¹).im = -z.im/U := by rw [Complex.inv_im,hUn]
  rw [hwr,abs_of_pos (div_pos hx hUp)] at hr
  rw [hwi,abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hy) hUp)] at hi
  obtain ⟨hgl,hgu⟩ := septic_leading_error_bounds
  have hrlo := (abs_le.mp hr).1
  have hrhi := (abs_le.mp hr).2
  have hilo := (abs_le.mp hi).1
  have hihi := (abs_le.mp hi).2
  have hAr : (septicRemainder z).re/z.re = septicLeadingError/U+(septicError z⁻¹).re/z.re := by
    simp only [septicRemainder,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hwr]
    field_simp
  have hBi : (septicRemainder z).im/z.im = -septicLeadingError/U+(septicError z⁻¹).im/z.im := by
    simp only [septicRemainder,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,hwi]
    field_simp
  have herlo : -(3/200)/U ≤ (septicError z⁻¹).re/z.re := by
    have hh := div_le_div_of_nonneg_right hrlo hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have herhi : (septicError z⁻¹).re/z.re ≤ (3/200)/U := by
    have hh := div_le_div_of_nonneg_right hrhi hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heilo : -(3/200)/U ≤ (septicError z⁻¹).im/z.im := by
    have hh := div_le_div_of_nonneg_right hilo hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heihi : (septicError z⁻¹).im/z.im ≤ (3/200)/U := by
    have hh := div_le_div_of_nonneg_right hihi hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  simp only [neg_div] at herlo heilo
  have hAlo : (septicLeadingError-3/200)/U ≤ (septicRemainder z).re/z.re := by
    rw [hAr,sub_div]
    linarith
  have hAhi : (septicRemainder z).re/z.re ≤ (septicLeadingError+3/200)/U := by
    rw [hAr,add_div]
    linarith
  have hBlo : -(septicLeadingError+3/200)/U ≤ (septicRemainder z).im/z.im := by
    simp only [hBi,neg_div,add_div]
    linarith
  have hBhi : (septicRemainder z).im/z.im ≤ -(septicLeadingError-3/200)/U := by
    simp only [hBi,neg_div,sub_div]
    linarith
  simp only [neg_div] at hBlo hBhi
  have hsmall : (septicLeadingError+3/200)/U ≤ 27/2000 := by
    apply (div_le_iff₀ hUp).mpr
    linarith
  have hpos : 0 < (septicLeadingError-3/200)/U := div_pos (by linarith) hUp
  have hApos := lt_of_lt_of_le hpos hAlo
  have hBneg : (septicRemainder z).im/z.im < 0 := by linarith
  refine ⟨hApos,hAhi.trans hsmall,by linarith,hBneg,by linarith,?_,?_,?_⟩
  · intro hX4
    have hU4 : 4 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
    have hsmall4 : (septicLeadingError+3/200)/U ≤ 9/800 := by
      apply (div_le_iff₀ hUp).mpr
      linarith
    linarith
  · apply hAhi.trans
    exact div_le_div_of_nonneg_right (by linarith) hUp.le
  · have hh : (septicLeadingError+3/200)/U ≤ (9/200)/U :=
      div_le_div_of_nonneg_right (by linarith) hUp.le
    change -(9/200)/U ≤ _
    rw [neg_div]
    linarith

end DerivativeChainPrivate

end


section
-- Source module: QuadraticParameter


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem real_quadratic_root_im_of_nonzero_leading (A B C : ℝ) (hA : A ≠ 0)
    (hD : 0 ≤ B^2-4*A*C) (z : ℂ)
    (hroot : (A:ℂ)*z^2+(B:ℂ)*z+(C:ℂ)=0) : z.im=0 := by
  by_cases hC : C ≠ 0
  · exact real_quadratic_nonnegative_discriminant_root_im A B C hC hD z hroot
  · have hC0 := not_ne_iff.mp hC
    rw [hC0,Complex.ofReal_zero,add_zero] at hroot
    have hp : z*((A:ℂ)*z+(B:ℂ))=0 := by linear_combination hroot
    rcases mul_eq_zero.mp hp with he|he
    · simp [he]
    · have hi := congrArg Complex.im he
      simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero,Complex.zero_im] at hi
      exact (mul_eq_zero.mp hi).resolve_left hA

end DerivativeChainPrivate

end


section
-- Source module: FourthSepticScalars


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_septic_scalar_gaps :
    let α₆ := (28-3*Real.sqrt 70)/55
    let b₆ := (35-3*Real.sqrt 70)/50
    let αm := (7-3*Real.sqrt 3)/55
    let bm := 7*(3-Real.sqrt 3)/60
    let αp := (7+3*Real.sqrt 3)/55
    let bp := 7*(3+Real.sqrt 3)/60
    3/100 < αm ∧ αm < α₆ ∧ 9/200 < b₆-bm ∧
      391/25000 < b₆-(10/3)*α₆ ∧
      1/5 < αp ∧ α₆ < αp ∧
      bp-b₆+391/25000 < (αp-α₆)*(10/3) ∧
      2*bp/3-b₆+3/40 < (8*αp/3-3*α₆)*(10/3) ∧
      27/2000 < bm-4*αm := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h70 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 70)
  have hp3 := Real.sqrt_nonneg 3
  have hp70 := Real.sqrt_nonneg 70
  have h3l : (1732/1000:ℝ) < Real.sqrt 3 := by nlinarith
  have h3u : Real.sqrt 3 < (1733/1000:ℝ) := by nlinarith
  have h70l : (8366/1000:ℝ) < Real.sqrt 70 := by nlinarith
  have h70u : Real.sqrt 70 < (8367/1000:ℝ) := by nlinarith
  dsimp only
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

end DerivativeChainPrivate

end


section
-- Source module: OcticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

















theorem octic_sqrt_remainder_identity (u : ℂ) :
    octicSqrtRadicand u-(octicSqrtPoly u)^2 = u^8*octicSqrtResidual u := by
  norm_num [octicSqrtRadicand,octicSqrtPoly,octicSqrtResidual,
    octicSqrtCoeffs,octicResidualCoeffs,Fin.sum_univ_succ]
  ring

theorem octic_expansion_identity (u : ℂ) :
    (14/275)-(7/30)*u+(11/60)*u^2-((3*Real.sqrt 26/550:ℝ):ℂ)*(1-(11/6)*u)^2*octicSqrtPoly u-
      ((((28-3*Real.sqrt 26)/550:ℝ):ℂ)-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)*u)*(1-(11/15)*u) =
    u^2*((1-(11/15)*u)*(∑ i : Fin 7, (octicExpansionCoeffs i:ℂ)*u^i.val)+
      u^7*(octicRationalTailCoeff:ℂ)) := by
  norm_num [octicSqrtPoly,octicSqrtCoeffs,octicExpansionCoeffs,octicRationalTailCoeff,Fin.sum_univ_succ]
  push_cast
  ring

theorem octic_sqrt_poly_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    ‖octicSqrtPoly u-1‖ ≤ 1/10 := by
  have hs := norm_real_power_sum_le octicSqrtCoeffs u (4/9) (by norm_num) hu
  calc
    _ = ‖u‖*‖∑ i : Fin 7, (octicSqrtCoeffs i:ℂ)*u^i.val‖ := by simp [octicSqrtPoly,norm_mul]
    _ ≤ (4/9)*(∑ i : Fin 7, |octicSqrtCoeffs i| * (4/9:ℝ)^i.val) :=
      mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _ ≤ 1/10 := by norm_num [octicSqrtCoeffs,Fin.sum_univ_succ]

theorem octic_sqrt_residual_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    ‖octicSqrtResidual u‖ ≤ 1/500000 := by
  apply (norm_real_power_sum_le octicResidualCoeffs u (4/9) (by norm_num) hu).trans
  norm_num [octicResidualCoeffs,Fin.sum_univ_succ]

theorem octic_sqrt_radicand_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    ‖octicSqrtRadicand u-1‖ ≤ 1/2 := by
  have he : octicSqrtRadicand u-1 = (11/39:ℂ)*u := by dsimp [octicSqrtRadicand]; ring
  rw [he]
  norm_num [norm_mul]
  linarith

theorem octic_sqrt_slit (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    octicSqrtRadicand u ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hn := octic_sqrt_radicand_bound u hu
  have hr := Complex.re_le_norm (1-octicSqrtRadicand u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  linarith

theorem octic_sqrt_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    Complex.sqrt (octicSqrtRadicand u)+octicSqrtPoly u ≠ 0 ∧
      ‖(Complex.sqrt (octicSqrtRadicand u)+octicSqrtPoly u)⁻¹‖ ≤ 2 := by
  have hs : 0 ≤ (Complex.sqrt (octicSqrtRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp := octic_sqrt_poly_bound u hu
  have hr := Complex.re_le_norm (1-octicSqrtPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd := Complex.re_le_norm (Complex.sqrt (octicSqrtRadicand u)+octicSqrtPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/2:ℝ) ≤ ‖Complex.sqrt (octicSqrtRadicand u)+octicSqrtPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

theorem octic_pole_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    1-(11/15:ℂ)*u ≠ 0 ∧ ‖(1-(11/15:ℂ)*u)⁻¹‖ ≤ 2 := by
  have hn := norm_sub_norm_le (1:ℂ) ((11/15:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (1/2:ℝ) ≤ ‖1-(11/15:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

theorem octic_coefficient_bounds :
    (17/1000:ℝ) < octicExpansionCoeffs 0 ∧ octicExpansionCoeffs 0 < 9/500 ∧
      |octicRationalTailCoeff| ≤ 1/100000 ∧
      ∀ i : Fin 6, |octicErrorCoeffs i| ≤ octicErrorCoeffBounds i := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 26)
  have hp := Real.sqrt_nonneg 26
  have hlo : (50990/10000:ℝ) < Real.sqrt 26 := by nlinarith
  have hhi : Real.sqrt 26 < (50991/10000:ℝ) := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [octicExpansionCoeffs]; linarith
  · norm_num [octicExpansionCoeffs]; linarith
  · rw [abs_le]
    dsimp [octicRationalTailCoeff]
    constructor <;> linarith
  · intro i
    fin_cases i <;> norm_num [octicErrorCoeffs,octicErrorCoeffBounds,abs_le] <;> constructor <;> linarith

end DerivativeChainPrivate

end


section
-- Source module: OcticTail


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem octic_tail_norm (w : ℂ) (hw : ‖w‖ ≤ 2/3) : ‖octicTail w‖ ≤ 1/1000000 := by
  have hu : ‖w^2‖ ≤ 4/9 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0 < (3*Real.sqrt 26/550:ℝ) := by positivity
  have hku : (3*Real.sqrt 26/550:ℝ) ≤ 3/100 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 26)
    have hp := Real.sqrt_nonneg 26
    nlinarith
  have hf : ‖1-(11/6:ℂ)*w^2‖ ≤ 49/27 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖(11/6:ℂ)*w^2‖ := norm_sub_le _ _
      _ = 1+(11/6:ℝ)*‖w^2‖ := by norm_num [norm_mul]
      _ ≤ 49/27 := by linarith
  have ht := octic_sqrt_residual_bound (w^2) hu
  have hd := (octic_sqrt_denominator_bound (w^2) hu).2
  have hp := (octic_pole_denominator_bound (w^2) hu).2
  have hL := octic_coefficient_bounds.2.2.1
  have h1 : ‖(octicRationalTailCoeff:ℂ)*w^15/(1-(11/15:ℂ)*w^2)‖ ≤ (1/100000:ℝ)*(2/3)^15*2 := by
    calc
      _ = |octicRationalTailCoeff| * ‖w‖^15*‖(1-(11/15:ℂ)*w^2)⁻¹‖ := by
        simp [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by gcongr
  have h2 : ‖((3*Real.sqrt 26/550:ℝ):ℂ)*w^13*(1-(11/6:ℂ)*w^2)^2*octicSqrtResidual (w^2)/
      (Complex.sqrt (octicSqrtRadicand (w^2))+octicSqrtPoly (w^2))/(1-(11/15:ℂ)*w^2)‖ ≤
      (3/100:ℝ)*(2/3)^13*(49/27)^2*(1/500000)*2*2 := by
    calc
      _ = (3*Real.sqrt 26/550:ℝ)*‖w‖^13*‖1-(11/6:ℂ)*w^2‖^2*‖octicSqrtResidual (w^2)‖*
          ‖(Complex.sqrt (octicSqrtRadicand (w^2))+octicSqrtPoly (w^2))⁻¹‖*‖(1-(11/15:ℂ)*w^2)⁻¹‖ := by
        simp only [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
        norm_num [abs_of_nonneg (Real.sqrt_nonneg 26)]
      _ ≤ _ := by gcongr
  unfold octicTail
  apply (norm_sub_le _ _).trans
  have hh := add_le_add h1 h2
  apply hh.trans
  norm_num

theorem octic_tail_differentiableAt (w : ℂ) (hw : ‖w‖ ≤ 2/3) :
    DifferentiableAt ℂ octicTail w := by
  have hu : ‖w^2‖ ≤ 4/9 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => octicSqrtRadicand (v^2)) w := by
    unfold octicSqrtRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (octicSqrtRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (octic_sqrt_slit (w^2) hu)).comp w hh
  have hpoly : DifferentiableAt ℂ (fun v : ℂ => octicSqrtPoly (v^2)) w := by unfold octicSqrtPoly; fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => octicSqrtResidual (v^2)) w := by unfold octicSqrtResidual; fun_prop
  have hd := (octic_sqrt_denominator_bound (w^2) hu).1
  have hp := (octic_pole_denominator_bound (w^2) hu).1
  unfold octicTail
  fun_prop

theorem octic_tail_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 3/10) :
    ‖deriv octicTail w‖ ≤ 1/50000 := by
  have hw' : ‖w‖ ≤ 11/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/10:ℝ), ‖u‖ ≤ 2/3 := by
    intro u hu
    have hd : ‖u-w‖ < 1/10 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ octicTail (Metric.ball w (1/10:ℝ)) := by
    intro u hu
    exact (octic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo octicTail (Metric.ball w (1/10:ℝ))
      (Metric.closedBall (octicTail w) (1/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := octic_tail_norm u (hball u hu)
    have h2 := octic_tail_norm w (by linarith)
    have hn := norm_sub_le (octicTail u) (octicTail w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/10)
  norm_num at hh
  exact hh

end DerivativeChainPrivate

end


section
-- Source module: OcticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators




theorem octic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt octicPolynomialError
      (∑ i : Fin 6, (octicErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)) w := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (octicErrorCoeffs i:ℂ)

theorem octic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 1/4) :
    ‖deriv octicPolynomialError w‖ ≤ 3/2000 := by
  rw [(octic_polynomial_error_hasDerivAt w).deriv]
  have hsum : ‖∑ i : Fin 6, (octicErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 6, octicErrorCoeffBounds i * ((2*i.val+3:ℕ):ℝ)*(1/4:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    have hb := octic_coefficient_bounds.2.2.2 i
    have hb0 : 0 ≤ octicErrorCoeffBounds i := (abs_nonneg _).trans hb
    gcongr
  apply hsum.trans
  norm_num [octicErrorCoeffBounds,Fin.sum_univ_succ]

theorem octic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2 ≤ 1/4) :
    DifferentiableAt ℂ octicError w := by
  have hn : ‖w‖ ≤ 2/3 := by nlinarith [norm_nonneg w]
  exact (octic_polynomial_error_hasDerivAt w).differentiableAt.add (octic_tail_differentiableAt w hn)

theorem octic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 1/4) :
    ‖deriv octicError w‖ ≤ 1/500 := by
  have hn : ‖w‖ ≤ 2/3 := by nlinarith [norm_nonneg w]
  have hp := octic_polynomial_error_deriv_bound w hw
  have ht := octic_tail_deriv_bound w (by linarith)
  have hd : deriv octicError w = deriv octicPolynomialError w+deriv octicTail w := by
    exact deriv_add (octic_polynomial_error_hasDerivAt w).differentiableAt (octic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv octicPolynomialError w) (deriv octicTail w)
  linarith

end DerivativeChainPrivate

end


section
-- Source module: OcticAxes


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem octic_radicand_real (x : ℝ) : octicSqrtRadicand (x:ℂ) = ((1+(11/39)*x:ℝ):ℂ) := by
  simp [octicSqrtRadicand]
theorem octic_poly_real (x : ℝ) : octicSqrtPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 7, octicSqrtCoeffs i*x^i.val):ℝ):ℂ) := by simp [octicSqrtPoly]
theorem octic_residual_real (x : ℝ) : octicSqrtResidual (x:ℂ) =
    ((∑ i : Fin 7, octicResidualCoeffs i*x^i.val : ℝ):ℂ) := by simp [octicSqrtResidual]
theorem octic_sqrt_real (x : ℝ) (hx : -4/9 ≤ x) : Complex.sqrt (octicSqrtRadicand (x:ℂ)) =
    ((Real.sqrt (1+(11/39)*x):ℝ):ℂ) := by
  have hp : 0 ≤ 1+(11/39:ℝ)*x := by linarith
  rw [octic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp),Complex.ofReal_re]

theorem octic_tail_real_axis (x : ℝ) : (octicTail (x:ℂ)).im = 0 := by
  unfold octicTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [octic_sqrt_real _ (by nlinarith [sq_nonneg x]),octic_poly_real,octic_residual_real]
  rw [show (x:ℂ)^13=((x^13:ℝ):ℂ) by norm_cast,show (x:ℂ)^15=((x^15:ℝ):ℂ) by norm_cast]
  rw [show (11/6:ℂ)=((11/6:ℝ):ℂ) by norm_num,show (11/15:ℂ)=((11/15:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,← Complex.ofReal_pow,Complex.ofReal_im]

theorem octic_tail_imaginary_axis (x : ℝ) (hx : x^2 ≤ 4/9) : (octicTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold octicTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [octic_sqrt_real _ (by linarith),octic_poly_real,octic_residual_real]
  have he13 : (Complex.I*(x:ℂ))^13 = Complex.I*((x^13:ℝ):ℂ) := by norm_num [mul_pow,Complex.I_pow_eq_pow_mod]
  have he15 : (Complex.I*(x:ℂ))^15 = -Complex.I*((x^15:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod] <;> norm_num [Complex.I_pow_three]
  rw [he13,he15]
  rw [show (11/6:ℂ)=((11/6:ℝ):ℂ) by norm_num,show (11/15:ℂ)=((11/15:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,← Complex.ofReal_pow]
  simp only [Complex.sub_re,Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,zero_sub,mul_one,one_mul,neg_zero,zero_div]

theorem octic_error_axes (x : ℝ) (hx : x^2 ≤ 4/9) :
    (octicError (x:ℂ)).im = 0 ∧ (octicError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [octicError,Complex.add_im,octic_tail_real_axis,add_zero]
    norm_num [octicPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [octicError,Complex.add_re,octic_tail_imaginary_axis x hx,add_zero]
    norm_num [octicPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]

end DerivativeChainPrivate

end


section
-- Source module: OcticCoordinates


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem octic_error_coordinate_bounds (w : ℂ) (hw : ‖w‖^2 ≤ 1/4) :
    |(octicError w).re| ≤ (1/500)*|w.re| ∧
      |(octicError w).im| ≤ (1/500)*|w.im| := by
  let S := Metric.closedBall (0:ℂ) ‖w‖
  have hs (v : ℂ) (hv : v ∈ S) : ‖v‖^2 ≤ 1/4 := by
    have hn : ‖v‖ ≤ ‖w‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hw
  have hd : ∀ v ∈ S, DifferentiableAt ℂ octicError v := fun v hv => octic_error_differentiableAt v (hs v hv)
  have hb : ∀ v ∈ S, ‖deriv octicError v‖ ≤ 1/500 := fun v hv => octic_error_deriv_bound v (hs v hv)
  have hc : Convex ℝ S := convex_closedBall (0:ℂ) ‖w‖
  have hwm : w ∈ S := by simp [S]
  have hxr : (w.re:ℂ) ∈ S := by
    simpa only [S,Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using Complex.abs_re_le_norm w
  have hyi : Complex.I*(w.im:ℂ) ∈ S := by
    simpa only [S,Metric.mem_closedBall,dist_zero_right,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs] using Complex.abs_im_le_norm w
  have hsq : ‖w‖^2 = w.re^2+w.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  have hr2 : w.re^2 ≤ 4/9 := by nlinarith [sq_nonneg w.im]
  have hi2 : w.im^2 ≤ 4/9 := by nlinarith [sq_nonneg w.re]
  constructor
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hyi hwm
    have he : w-Complex.I*(w.im:ℂ) = (w.re:ℂ) := by apply Complex.ext <;> simp
    rw [he,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_re_le_norm (octicError w-octicError (Complex.I*(w.im:ℂ)))
    rw [Complex.sub_re,(octic_error_axes w.im hi2).2,sub_zero] at hp
    exact hp.trans hh
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hxr hwm
    have he : w-(w.re:ℂ) = Complex.I*(w.im:ℂ) := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_im_le_norm (octicError w-octicError (w.re:ℂ))
    rw [Complex.sub_im,(octic_error_axes w.re hr2).1,sub_zero] at hp
    exact hp.trans hh




theorem octic_leading_error_bounds : (17/1000:ℝ) < octicLeadingError ∧ octicLeadingError < 9/500 :=
  ⟨octic_coefficient_bounds.1,octic_coefficient_bounds.2.1⟩

theorem octic_remainder_coordinate_bounds (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im)
    (hX : 4 ≤ z.re^2) :
    0 < (octicRemainder z).re/z.re ∧ (octicRemainder z).re/z.re ≤ 1/200 ∧
      -(1/200) ≤ (octicRemainder z).im/z.im ∧ (octicRemainder z).im/z.im < 0 ∧
      0 < (3*((octicRemainder z).re/z.re)-(octicRemainder z).im/z.im)/2 ∧
      (3*((octicRemainder z).re/z.re)-(octicRemainder z).im/z.im)/2 ≤ 1/100 ∧
      (octicRemainder z).re/z.re ≤ (1/50)/(z.re^2+z.im^2) ∧
      -(1/50)/(z.re^2+z.im^2) ≤ (octicRemainder z).im/z.im := by
  let U := z.re^2+z.im^2
  have hU : 4 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith
  have hUn : Complex.normSq z = U := by simp [U,Complex.normSq_apply,pow_two]
  have hn : ‖z⁻¹‖^2 ≤ 1/4 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,hUn]
    exact (inv_le_comm₀ hUp (by norm_num)).mpr (by norm_num; exact hU)
  obtain ⟨hr,hi⟩ := octic_error_coordinate_bounds z⁻¹ hn
  have hwr : (z⁻¹).re = z.re/U := by rw [Complex.inv_re,hUn]
  have hwi : (z⁻¹).im = -z.im/U := by rw [Complex.inv_im,hUn]
  rw [hwr,abs_of_pos (div_pos hx hUp)] at hr
  rw [hwi,abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hy) hUp)] at hi
  obtain ⟨hgl,hgu⟩ := octic_leading_error_bounds
  have hrlo := (abs_le.mp hr).1
  have hrhi := (abs_le.mp hr).2
  have hilo := (abs_le.mp hi).1
  have hihi := (abs_le.mp hi).2
  have hAr : (octicRemainder z).re/z.re = octicLeadingError/U+(octicError z⁻¹).re/z.re := by
    simp only [octicRemainder,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hwr]
    field_simp
  have hBi : (octicRemainder z).im/z.im = -octicLeadingError/U+(octicError z⁻¹).im/z.im := by
    simp only [octicRemainder,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,hwi]
    field_simp
  have herlo : -(1/500)/U ≤ (octicError z⁻¹).re/z.re := by
    have hh := div_le_div_of_nonneg_right hrlo hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have herhi : (octicError z⁻¹).re/z.re ≤ (1/500)/U := by
    have hh := div_le_div_of_nonneg_right hrhi hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heilo : -(1/500)/U ≤ (octicError z⁻¹).im/z.im := by
    have hh := div_le_div_of_nonneg_right hilo hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heihi : (octicError z⁻¹).im/z.im ≤ (1/500)/U := by
    have hh := div_le_div_of_nonneg_right hihi hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  simp only [neg_div] at herlo heilo
  have hAlo : (octicLeadingError-1/500)/U ≤ (octicRemainder z).re/z.re := by
    rw [hAr,sub_div]
    linarith
  have hAhi : (octicRemainder z).re/z.re ≤ (octicLeadingError+1/500)/U := by
    rw [hAr,add_div]
    linarith
  have hBlo : -(octicLeadingError+1/500)/U ≤ (octicRemainder z).im/z.im := by
    simp only [hBi,neg_div,add_div]
    linarith
  have hBhi : (octicRemainder z).im/z.im ≤ -(octicLeadingError-1/500)/U := by
    simp only [hBi,neg_div,sub_div]
    linarith
  simp only [neg_div] at hBlo hBhi
  have hsmall : (octicLeadingError+1/500)/U ≤ 1/200 := by
    apply (div_le_iff₀ hUp).mpr
    linarith
  have hpos : 0 < (octicLeadingError-1/500)/U := div_pos (by linarith) hUp
  have hApos := lt_of_lt_of_le hpos hAlo
  have hBneg : (octicRemainder z).im/z.im < 0 := by linarith
  refine ⟨hApos,hAhi.trans hsmall,by linarith,hBneg,by linarith,?_,?_,?_⟩
  · linarith
  · apply hAhi.trans
    exact div_le_div_of_nonneg_right (by linarith) hUp.le
  · have hh : (octicLeadingError+1/500)/U ≤ (1/50)/U :=
      div_le_div_of_nonneg_right (by linarith) hUp.le
    change -(1/50)/U ≤ _
    rw [neg_div]
    linarith

end DerivativeChainPrivate

end


section
-- Source module: OcticInverseAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem octic_sqrt_exact_remainder (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    Complex.sqrt (octicSqrtRadicand u) = octicSqrtPoly u+
      u^8*octicSqrtResidual u/(Complex.sqrt (octicSqrtRadicand u)+octicSqrtPoly u) := by
  have hd := (octic_sqrt_denominator_bound u hu).1
  have hs : (Complex.sqrt (octicSqrtRadicand u))^2 = octicSqrtRadicand u :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have he : (Complex.sqrt (octicSqrtRadicand u)-octicSqrtPoly u)*
      (Complex.sqrt (octicSqrtRadicand u)+octicSqrtPoly u) = u^8*octicSqrtResidual u := by
    calc
      _ = (Complex.sqrt (octicSqrtRadicand u))^2-(octicSqrtPoly u)^2 := by ring
      _ = _ := by rw [hs,octic_sqrt_remainder_identity]
  have hh := (eq_div_iff hd).mpr he
  linear_combination hh

theorem octic_polynomial_error_identity (w : ℂ) :
    (octicLeadingError:ℂ)*w+octicPolynomialError w =
      w*(∑ i : Fin 7, (octicExpansionCoeffs i:ℂ)*(w^2)^i.val) := by
  norm_num [octicLeadingError,octicPolynomialError,octicExpansionCoeffs,octicErrorCoeffs,Fin.sum_univ_succ]
  ring

theorem octic_remainder_scaled (w : ℂ) (hw : ‖w^2‖ ≤ 4/9) :
    w^3*(1-(11/15)*w^2)*((octicLeadingError:ℂ)*w+octicError w) =
      (14/275)-(7/30)*w^2+(11/60)*w^4-
      ((3*Real.sqrt 26/550:ℝ):ℂ)*(1-(11/6)*w^2)^2*Complex.sqrt (octicSqrtRadicand (w^2))-
      ((((28-3*Real.sqrt 26)/550:ℝ):ℂ)-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)*w^2)*(1-(11/15)*w^2) := by
  have hp := (octic_pole_denominator_bound (w^2) hw).1
  have hs := octic_sqrt_exact_remainder (w^2) hw
  have he : Complex.sqrt (octicSqrtRadicand (w^2))-octicSqrtPoly (w^2) =
      (w^2)^8*octicSqrtResidual (w^2)/(Complex.sqrt (octicSqrtRadicand (w^2))+octicSqrtPoly (w^2)) := by
    linear_combination hs
  have htail : (1-(11/15:ℂ)*w^2)*octicTail w =
      (octicRationalTailCoeff:ℂ)*w^15-
      ((3*Real.sqrt 26/550:ℝ):ℂ)*w^13*(1-(11/6:ℂ)*w^2)^2*octicSqrtResidual (w^2)/
        (Complex.sqrt (octicSqrtRadicand (w^2))+octicSqrtPoly (w^2)) := by
    unfold octicTail
    rw [mul_sub,← mul_div_assoc,← mul_div_assoc,
      mul_div_cancel_left₀ _ hp,mul_div_cancel_left₀ _ hp]
  calc
    _ = (w^2)^2*((1-(11/15)*w^2)*(∑ i : Fin 7, (octicExpansionCoeffs i:ℂ)*(w^2)^i.val)+
          (w^2)^7*(octicRationalTailCoeff:ℂ))-
        ((3*Real.sqrt 26/550:ℝ):ℂ)*(1-(11/6)*w^2)^2*
          (Complex.sqrt (octicSqrtRadicand (w^2))-octicSqrtPoly (w^2)) := by
      unfold octicError
      rw [← add_assoc,octic_polynomial_error_identity,he]
      linear_combination w^3*htail
    _ = _ := by rw [← octic_expansion_identity]; ring

theorem octic_inverse_exact (z : ℂ) (hz : z ≠ 0) (hn : ‖z⁻¹‖^2 ≤ 1/4) :
    (((28-3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder z/z =
      ((14/275)*z^4-(7/30)*z^2+11/60-
        ((3*Real.sqrt 26/550:ℝ):ℂ)*(z^2-11/6)^2*Complex.sqrt (octicSqrtRadicand ((z⁻¹)^2)))/(z^2-11/15) := by
  have hw : ‖(z⁻¹)^2‖ ≤ 4/9 := by rw [norm_pow]; linarith
  have hp := (octic_pole_denominator_bound ((z⁻¹)^2) hw).1
  have hzpole : z^2-(11/15:ℂ) ≠ 0 := by
    intro he
    apply hp
    field_simp
    linear_combination (15:ℂ)*he
  have hS := octic_remainder_scaled z⁻¹ hw
  change (z⁻¹)^3*(1-(11/15)*(z⁻¹)^2)*octicRemainder z = _ at hS
  apply (eq_div_iff hzpole).mpr
  calc
    _ = ((((28-3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder z/z)*(z^2-11/15)-
        z^4*((z⁻¹)^3*(1-(11/15)*(z⁻¹)^2)*octicRemainder z-
          ((14/275)-(7/30)*(z⁻¹)^2+(11/60)*(z⁻¹)^4-
          ((3*Real.sqrt 26/550:ℝ):ℂ)*(1-(11/6)*(z⁻¹)^2)^2*Complex.sqrt (octicSqrtRadicand ((z⁻¹)^2))-
          ((((28-3*Real.sqrt 26)/550:ℝ):ℂ)-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)*(z⁻¹)^2)*(1-(11/15)*(z⁻¹)^2))) := by
      rw [hS]
      ring
    _ = _ := by field_simp; ring

end DerivativeChainPrivate

end


section
-- Source module: FourthOcticGraphs


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_octic_upper_graphs (β z : ℂ) (hx : 0 < z.re) (hX : 4 ≤ z.re^2)
    (hroot : z^8-(28/3)*z^6-56*β*z^5+(77/3)*z^4+(770/3)*β*z^3-(121/6)*z^2+
      550*β^2*z^2-(605/3)*β*z+1331/720-(1210/3)*β^2=0) :
    β/z = (((28-3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder z/z ∨
    β/z = (((28+3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274+99*Real.sqrt 26)/6500:ℝ):ℂ)+
      ((99/1250)*z/(z^2-11/15)-octicRemainder z)/z := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hnorm : 4 ≤ ‖z‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  have hn : ‖z⁻¹‖^2 ≤ 1/4 := by
    rw [norm_inv,inv_pow]
    apply (inv_le_comm₀ (by positivity : 0 < ‖z‖^2) (by norm_num)).mpr
    norm_num
    exact hnorm
  have hu : ‖(z⁻¹)^2‖ ≤ 4/9 := by rw [norm_pow]; linarith
  have hpole := (octic_pole_denominator_bound ((z⁻¹)^2) hu).1
  have hzp : z^2-(11/15:ℂ) ≠ 0 := by
    intro he
    apply hpole
    field_simp
    linear_combination (15:ℂ)*he
  let S := Complex.sqrt (octicSqrtRadicand ((z⁻¹)^2))
  let s : ℂ := (Real.sqrt 26:ℂ)
  have hs : s^2=26 := by dsimp [s]; rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hS : S^2=octicSqrtRadicand ((z⁻¹)^2) := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hd : ((1100*z^2-2420/3)*β-56*z^5+(770/3)*z^3-(605/3)*z)^2 =
      936*(z^2+11/39)*(z^2-11/6)^4 := by
    linear_combination 4*(550*z^2-1210/3)*hroot
  have hsquare : (6*s*z*(z^2-11/6)^2*S)^2 = 936*(z^2+11/39)*(z^2-11/6)^4 := by
    calc
      _ = 36*s^2*z^2*(z^2-11/6)^4*S^2 := by ring
      _ = _ := by rw [hs,hS]; unfold octicSqrtRadicand; field_simp; ring
  have hsplit := (sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  have hbase : β/z = ((14/275)*z^4-(7/30)*z^2+11/60-(3*s/550)*(z^2-11/6)^2*S)/(z^2-11/15) ∨
      β/z = ((14/275)*z^4-(7/30)*z^2+11/60+(3*s/550)*(z^2-11/6)^2*S)/(z^2-11/15) := by
    rcases hsplit with hp|hm
    · right
      have hv : β/z = (56*z^4-(770/3)*z^2+605/3+6*s*(z^2-11/6)^2*S)/(1100*(z^2-11/15)) := by
        apply (div_eq_div_iff hz (mul_ne_zero (by norm_num) hzp)).mpr
        linear_combination hp
      rw [hv]
      field_simp
      ring
    · left
      have hv : β/z = (56*z^4-(770/3)*z^2+605/3-6*s*(z^2-11/6)^2*S)/(1100*(z^2-11/15)) := by
        apply (div_eq_div_iff hz (mul_ne_zero (by norm_num) hzp)).mpr
        linear_combination hm
      rw [hv]
      field_simp
      ring
  have hminus := octic_inverse_exact z hz hn
  have hplus : (((28+3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274+99*Real.sqrt 26)/6500:ℝ):ℂ)+
      ((99/1250)*z/(z^2-11/15)-octicRemainder z)/z =
      ((14/275)*z^4-(7/30)*z^2+11/60+(3*s/550)*(z^2-11/6)^2*S)/(z^2-11/15) := by
    calc
      _ = (28/275)*z^2-49/125+(99/1250)/(z^2-11/15)-
          ((((28-3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder z/z) := by
        push_cast
        field_simp
        ring
      _ = _ := by
        rw [hminus]
        apply (eq_div_iff hzp).mpr
        rw [sub_mul,add_mul,div_mul_cancel₀ _ hzp,div_mul_cancel₀ _ hzp]
        dsimp only [s,S]
        push_cast
        ring
  rcases hbase with hm|hp
  · left
    rw [hminus]
    convert hm using 1 <;> dsimp only [s,S] <;> push_cast <;> ring
  · right
    rw [hplus]
    exact hp

end DerivativeChainPrivate

end


section
-- Source module: OcticPoleBounds


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem octic_pole_corrections (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 4 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    let E := (99/1250)*z/(z^2-11/15)
    (1/25)/U ≤ E.re/z.re ∧ E.re/z.re ≤ (1/10)/U ∧
      -(3/20)/U ≤ E.im/z.im ∧ E.im/z.im ≤ -(3/50)/U := by
  let U := z.re^2+z.im^2
  let D := ‖z^2-(11/15:ℂ)‖^2
  let E := (99/1250:ℂ)*z/(z^2-11/15)
  have hU : 4 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith
  have hUc : 0 < U-11/15 := by linarith
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hpole := (cauchy_root_kernel_bound z (by linarith) (11/15) (by constructor <;> norm_num)).1
  obtain ⟨hr,hi,_,hd⟩ := rational_inverse_parts E z 0 0 (99/1250) (11/15) hz hpole
    (by dsimp [E]; norm_num; field_simp)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,zero_mul,sub_zero,zero_add,zero_sub] at hr hi hd
  have hDlo : (U-11/15)^2 ≤ D := by
    dsimp only [D,U]
    nlinarith only [hd,sq_nonneg z.im]
  have hDhi : D ≤ (U+11/15)^2 := by
    dsimp only [D,U]
    nlinarith only [hd,sq_nonneg z.re]
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hUc) hDlo
  have hAr : E.re/z.re = (99/1250:ℝ)*(U-11/15)/D := by
    rw [hr]
    dsimp [U,D]
    field_simp
  have hBi : E.im/z.im = -(99/1250:ℝ)*(U+11/15)/D := by
    rw [hi]
    dsimp [U,D]
    field_simp <;> ring
  have hAlo : (1/25:ℝ)/U ≤ (99/1250)*(U-11/15)/D := by
    apply (div_le_div_iff₀ hUp hDp).mpr
    nlinarith [sq_nonneg (U-4)]
  have hAhi : (99/1250:ℝ)*(U-11/15)/D ≤ (1/10)/U := by
    apply (div_le_div_iff₀ hDp hUp).mpr
    nlinarith [sq_nonneg (U-4)]
  have hBlo : (3/50:ℝ)/U ≤ (99/1250)*(U+11/15)/D := by
    apply (div_le_div_iff₀ hUp hDp).mpr
    nlinarith [sq_nonneg (U-4)]
  have hBhi : (99/1250:ℝ)*(U+11/15)/D ≤ (3/20)/U := by
    apply (div_le_div_iff₀ hDp hUp).mpr
    nlinarith [sq_nonneg (U-4)]
  change (1/25:ℝ)/U ≤ E.re/z.re ∧ _
  rw [hAr,hBi]
  simp only [neg_mul,neg_div]
  exact ⟨hAlo,hAhi,by linarith,by linarith⟩

end DerivativeChainPrivate

end


section
-- Source module: FourthOcticScalars


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_octic_scalar_gaps :
    let α₇ := (7-3*Real.sqrt 3)/55
    let b₇ := 7*(3-Real.sqrt 3)/60
    let αm := (28-3*Real.sqrt 26)/550
    let bm := (1274-99*Real.sqrt 26)/6500
    let αp := (28+3*Real.sqrt 26)/550
    let bp := (1274+99*Real.sqrt 26)/6500
    1/50 < αm ∧ αm < α₇ ∧ 9/400 < b₇-bm ∧
      1/100 < bm-1/10 ∧ 1/55 < αm ∧ 7/100 < αp ∧ α₇ < αp ∧ α₇ < 1/25 ∧
      bp-b₇+27/2000 < (αp-α₇)*4 ∧
      2*bp/3-b₇+1/20 < (8*αp/3-3*α₇)*4 := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h26 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 26)
  have hp3 := Real.sqrt_nonneg 3
  have hp26 := Real.sqrt_nonneg 26
  have h3l : (1732/1000:ℝ) < Real.sqrt 3 := by nlinarith
  have h3u : Real.sqrt 3 < (1733/1000:ℝ) := by nlinarith
  have h26l : (50990/10000:ℝ) < Real.sqrt 26 := by nlinarith
  have h26u : Real.sqrt 26 < (50991/10000:ℝ) := by nlinarith
  dsimp only
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

end DerivativeChainPrivate

end


section
-- Source module: FourthOcticUpperData


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_octic_upper_data (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 4 ≤ z.re^2)
    (hroot : z^8-(28/3)*z^6-56*β*z^5+(77/3)*z^4+(770/3)*β*z^3-(121/6)*z^2+
      550*β^2*z^2-(605/3)*β*z+1331/720-(1210/3)*β^2=0) :
    ∃ α b : ℝ, ∃ e : ℂ, 1/50 < α ∧ β/z = (α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((α = (28-3*Real.sqrt 26)/550 ∧ b = (1274-99*Real.sqrt 26)/6500 ∧ e = octicRemainder z ∧
          0 ≤ (3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α = (28+3*Real.sqrt 26)/550 ∧ b = (1274+99*Real.sqrt 26)/6500 ∧
          0 ≤ e.re/z.re ∧ e.re/z.re ≤ 1/40 ∧ -(3/80) ≤ e.im/z.im ∧ e.im/z.im ≤ 0)) := by
  obtain ⟨hAp,hAu,hBl,hBn,hCp,hCu,hAr,hBr⟩ := octic_remainder_coordinate_bounds z hx hy hX
  obtain ⟨hαm,_,_,_,_,hαp,_,_,_,_⟩ := fourth_octic_scalar_gaps
  rcases fourth_octic_upper_graphs β z hx hX hroot with hm|hp
  · refine ⟨(28-3*Real.sqrt 26)/550,(1274-99*Real.sqrt 26)/6500,octicRemainder z,hαm,hm,?_,
      Or.inl ⟨rfl,rfl,rfl,hCp.le⟩⟩
    apply cubic_graph_positive_phase_of_corrections β z (octicRemainder z) _ _ (1/200)
      hx hy (by linarith) (by norm_num) (by linarith) hAu _ hm
    linarith only [hBl]
  · let U := z.re^2+z.im^2
    let P := (99/1250:ℂ)*z/(z^2-11/15)
    let E := P-octicRemainder z
    obtain ⟨hPAl,hPAu,hPBl,hPBu⟩ := octic_pole_corrections z hx hy hX
    change (1/25:ℝ)/U ≤ P.re/z.re at hPAl
    change P.re/z.re ≤ (1/10:ℝ)/U at hPAu
    change -(3/20:ℝ)/U ≤ P.im/z.im at hPBl
    change P.im/z.im ≤ -(3/50:ℝ)/U at hPBu
    change (octicRemainder z).re/z.re ≤ (1/50:ℝ)/U at hAr
    change -(1/50:ℝ)/U ≤ (octicRemainder z).im/z.im at hBr
    have hU : 4 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
    have hUp : 0 < U := by linarith
    have hArat : E.re/z.re = P.re/z.re-(octicRemainder z).re/z.re := by simp only [E,Complex.sub_re,sub_div]
    have hBrat : E.im/z.im = P.im/z.im-(octicRemainder z).im/z.im := by simp only [E,Complex.sub_im,sub_div]
    have hcmpA : (1/50:ℝ)/U ≤ (1/25:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hcmpB : (1/50:ℝ)/U ≤ (3/50:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hboundA : (1/10:ℝ)/U ≤ 1/40 := by apply (div_le_iff₀ hUp).mpr; linarith
    have hboundB : (3/20:ℝ)/U ≤ 3/80 := by apply (div_le_iff₀ hUp).mpr; linarith
    simp only [neg_div] at hPBl hPBu hBr
    have hA0 : 0 ≤ E.re/z.re := by rw [hArat]; linarith
    have hA1 : E.re/z.re ≤ 1/40 := by rw [hArat]; linarith
    have hB0 : -(3/80) ≤ E.im/z.im := by rw [hBrat]; linarith
    have hB1 : E.im/z.im ≤ 0 := by rw [hBrat]; linarith
    refine ⟨(28+3*Real.sqrt 26)/550,(1274+99*Real.sqrt 26)/6500,E,by linarith,hp,?_,
      Or.inr ⟨rfl,rfl,hA0,hA1,hB0,hB1⟩⟩
    apply cubic_graph_positive_phase_of_corrections β z E _ _ (1/25) hx hy (by linarith)
      (by norm_num) (by linarith) _ _ hp
    · linarith only [hA1]
    · linarith only [hB0]

end DerivativeChainPrivate

end


section
-- Source module: FourthOcticPhase


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_octic_real_root_parameter (β : ℂ) (x : ℝ) (hX : 4 ≤ x^2)
    (hroot : (x:ℂ)^8-(28/3)*(x:ℂ)^6-56*β*(x:ℂ)^5+(77/3)*(x:ℂ)^4+(770/3)*β*(x:ℂ)^3-
      (121/6)*(x:ℂ)^2+550*β^2*(x:ℂ)^2-(605/3)*β*(x:ℂ)+1331/720-(1210/3)*β^2=0) : β.im=0 := by
  let A := (550:ℝ)*x^2-1210/3
  let B := -56*x^5+(770/3)*x^3-(605/3)*x
  let C := x^8-(28/3)*x^6+(77/3)*x^4-(121/6)*x^2+1331/720
  have hquad : (A:ℂ)*β^2+(B:ℂ)*β+(C:ℂ)=0 := by
    dsimp [A,B,C]; push_cast; linear_combination hroot
  apply real_quadratic_root_im_of_nonzero_leading A B C (by dsimp [A]; linarith) _ β hquad
  have he : B^2-4*A*C = 936*(x^2+11/39)*(x^2-11/6)^4 := by dsimp [A,B,C]; ring
  rw [he]
  positivity

theorem fourth_octic_nonnegative_im (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 4 ≤ z.re^2)
    (hroot : z^8-(28/3)*z^6-56*β*z^5+(77/3)*z^4+(770/3)*β*z^3-(121/6)*z^2+
      550*β^2*z^2-(605/3)*β*z+1331/720-(1210/3)*β^2=0) :
    0 ≤ z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0 ≤ z.im := by
    by_contra hn
    have hy : z.im < 0 := lt_of_not_ge hn
    have hroot' : (starRingEnd ℂ z)^8-(28/3)*(starRingEnd ℂ z)^6-56*(starRingEnd ℂ β)*(starRingEnd ℂ z)^5+
        (77/3)*(starRingEnd ℂ z)^4+(770/3)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^3-(121/6)*(starRingEnd ℂ z)^2+
        550*(starRingEnd ℂ β)^2*(starRingEnd ℂ z)^2-(605/3)*(starRingEnd ℂ β)*(starRingEnd ℂ z)+1331/720-
        (1210/3)*(starRingEnd ℂ β)^2=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fourth_octic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
      (by simpa using hx) (by simpa using neg_pos.mpr hy) (by simpa using hX) hroot'
    have hrat : 0 ≤ (β/z).im := by
      rw [Complex.div_im,← sub_div]
      apply div_nonneg
      · have h1 := mul_nonneg hI hx.le
        have h2 := mul_nonpos_of_nonneg_of_nonpos hR hy.le
        linarith
      · exact Complex.normSq_nonneg z
    have he : (starRingEnd ℂ β)/(starRingEnd ℂ z) = starRingEnd ℂ (β/z) := by simp
    rw [he,Complex.conj_im] at hp
    linarith
  refine ⟨hnonneg,?_⟩
  constructor
  · intro hβ
    by_contra hzero
    have hy : 0 < z.im := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    obtain ⟨α,b,e,_,_,hp,_⟩ := fourth_octic_upper_data β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    exact fourth_octic_real_root_parameter β z.re hX hroot

end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 4 ≤ w.re^2)
    (hwroot : (275/2)*β^2*w-35*β*w^4+(385/4)*β*w^2-(605/24)*β+
      w^7-7*w^5+(77/6)*w^3-(121/24)*w=0)
    (hwinv : β/w = (((7-3*Real.sqrt 3)/55:ℝ):ℂ)*w^2-((7*(3-Real.sqrt 3)/60:ℝ):ℂ)+septicRemainder w/w) :
    ∃ z : ℂ,
      z^8-(28/3)*z^6-56*β*z^5+(77/3)*z^4+(770/3)*β*z^3-(121/6)*z^2+
        550*β^2*z^2-(605/3)*β*z+1331/720-(1210/3)*β^2=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧
      β/z = (((28-3*Real.sqrt 26)/550:ℝ):ℂ)*z^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder z/z := by
  let α₀ := (7-3*Real.sqrt 3)/55
  let b₀ := 7*(3-Real.sqrt 3)/60
  let E₀ := septicRemainder w
  obtain ⟨hαm,hαm7,hgap,_,_,hαp,hα7p,hα₀up,hgapSE,hgapNE⟩ := fourth_octic_scalar_gaps
  change α₀ < 1/25 at hα₀up
  have hα₀ : 0 < α₀ := by have hh := fourth_septic_scalar_gaps; dsimp [α₀]; linarith [hh.1]
  obtain ⟨_,hA₀hi,_,hB₀hi,_,hC₀hi,_,_⟩ := septic_remainder_coordinate_bounds w hwpos hwim (by linarith)
  have hC₀ : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 9/400 := hC₀hi hwX
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  obtain ⟨hr₀,hi₀,_⟩ := cubic_graph_coordinate_parts β w E₀ α₀ b₀ hw hwinv
  have hR₀ : β.re/w.re = α₀*(w.re^2-3*w.im^2)-b₀+E₀.re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im = α₀*(3*w.re^2-w.im^2)-b₀+E₀.im/w.im := by rw [hi₀]; field_simp
  have hWedge : 4 ≤ w.re^2-3*w.im^2 := by
    have hh : 0 ≤ β.re/w.re := div_nonneg hR hwpos.le
    rw [hR₀] at hh
    have hslack := fourth_septic_scalar_gaps.2.2.2.2.2.2.2.2
    change 27/2000 < b₀-4*α₀ at hslack
    have ht : α₀*4 < α₀*(w.re^2-3*w.im^2) := by linarith
    exact (lt_of_mul_lt_mul_left ht hα₀.le).le
  let p : Polynomial ℂ := X^8-C (28/3)*X^6-C (56*β)*X^5+C (77/3)*X^4+
    C ((770/3)*β)*X^3+C (550*β^2-121/6)*X^2-C ((605/3)*β)*X+C (1331/720-(1210/3)*β^2)
  have hpdeg : p.natDegree=8 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w=0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 8*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 4 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hzroot : z^8-(28/3)*z^6-56*β*z^5+(77/3)*z^4+(770/3)*β*z^3-(121/6)*z^2+
      550*β^2*z^2-(605/3)*β*z+1331/720-(1210/3)*β^2=0 := by
    have he := hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at he
    linear_combination he
  obtain ⟨hy0,hzero⟩ := fourth_octic_nonnegative_im β z hR hI.le hx hX hzroot
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fourth_octic_upper_data β z hx hy hX hzroot
  obtain ⟨hr₁,hi₁,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  have hslow : α=(28-3*Real.sqrt 26)/550 ∧ b=(1274-99*Real.sqrt 26)/6500 ∧ e=octicRemainder z ∧
      0 ≤ (3*(e.re/z.re)-e.im/z.im)/2 := by
    rcases hcases with hs|⟨ha,hb,hAlo,hAhi,hBlo,hBhi⟩
    · exact hs
    · exfalso
      subst α
      subst b
      by_cases hvy : z.im ≤ w.im
      · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ _ b₀ _
          (E₀.re/w.re) (e.re/z.re) 4 (27/2000) 0 hR hwpos hy.le hxz hvy hWedge
          (by linarith) hα7p hA₀hi hAlo (by simpa [α₀,b₀] using hgapSE) hR₀ hR₁
      · exact fast_graph_northeast_impossible α₀ _ b₀ _ (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
          4 (1/20) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
          hR hI.le hwX hα₀.le (by linarith) (by linarith) hB₀hi.le (by linarith) hgapNE hI₀ hR₁ hI₁
  rcases hslow with ⟨rfl,rfl,rfl,hC₁⟩
  have himorder : w.im ≤ z.im := by
    by_contra hn
    exact inverse_graph_southeast_impossible α₀ _ b₀ _ (E₀.re/w.re) ((octicRemainder z).re/z.re)
      (E₀.im/w.im) ((octicRemainder z).im/z.im) (9/400) β.re β.im w.re w.im z.re z.im
      (by linarith) hαm7 hwpos hy hxz (le_of_not_ge hn) hR hI.le hC₀ hC₁ hgap hR₀ hI₀ hR₁ hI₁
  exact ⟨z,hzroot,hxz,himorder,hgraph⟩
