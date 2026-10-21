-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_septic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T18:53:50.724792+00:00
-- url     : https://prove2.me/submissions/bad72b6b-c201-4c84-b4fd-7cd4d1022b37

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Mathlib
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


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











end DerivativeChainPrivate

end


section
-- Source module: FifthSepticAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators






theorem fifth_septic_remainder_identity (u : ℂ) :
    fifthSepticRadicand u-(fifthSepticPoly u)^2=u^25*fifthSepticResidual u := by
  norm_num [fifthSepticRadicand,fifthSepticPoly,fifthSepticResidual,
    fifthSepticCoeffs,fifthSepticResidualCoeffs,Fin.sum_univ_succ]
  ring

theorem fifth_septic_poly_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    ‖fifthSepticPoly u-1‖ ≤ 3/4 := by
  have hs := norm_real_power_sum_le fifthSepticCoeffs u (9/4) (by norm_num) hu
  calc
    _ = ‖u‖*‖∑ i : Fin 24, (fifthSepticCoeffs i:ℂ)*u^i.val‖ := by simp [fifthSepticPoly,norm_mul]
    _ ≤ (9/4)*(∑ i : Fin 24, |fifthSepticCoeffs i| *(9/4:ℝ)^i.val) :=
      mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _ ≤ 3/4 := by norm_num [fifthSepticCoeffs,Fin.sum_univ_succ]

theorem fifth_septic_residual_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    ‖fifthSepticResidual u‖ ≤ 1/10000000000000000 := by
  apply (norm_real_power_sum_le fifthSepticResidualCoeffs u (9/4) (by norm_num) hu).trans
  norm_num [fifthSepticResidualCoeffs,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: GeneralGraphPhase

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_graph_positive_phase_general (β z e : ℂ) (α b M T : ℝ)
    (hx : 0 < z.re) (hy : 0 < z.im) (hX : T ≤ z.re^2) (hT : 0 < T)
    (hα : 0 < α) (hgap : M < α*T)
    (hA : e.re/z.re ≤ M) (hB : -M ≤ e.im/z.im)
    (hgraph : β/z = (α:ℂ)*z^2-(b:ℂ)+e/z) : 0 < (β/z).im := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hxy : 0 < 2*z.re*z.im := by positivity
  have hU : T ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < 2*(z.re^2+z.im^2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hU hα.le
  have hcorr : -α < (e.im/z.im-e.re/z.re)/(2*(z.re^2+z.im^2)) := by
    apply (lt_div_iff₀ hUp).mpr
    nlinarith only [hm,hgap,hA,hB]
  have hi := (cubic_graph_coordinate_parts β z e α b hz hgraph).2.2
  have hdiv : (β/z).im/(2*z.re*z.im) = α+(e/z).im/(2*z.re*z.im) := by
    rw [hi]; field_simp
  rw [quotient_imaginary_identity z e hx.ne' hy.ne'] at hdiv
  have hp : 0 < (β/z).im/(2*z.re*z.im) := by linarith
  exact (div_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticSlit

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate

theorem fifth_septic_radicand_positive (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    0 < (fifthSepticRadicand u).re := by
  let x := u.re
  let Y := u.im^2
  let V := (9/4:ℝ)^2-x^2
  have hx : |x| ≤ 9/4 := (Complex.abs_re_le_norm u).trans hu
  have hxlo : -(9/4:ℝ) ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ 9/4 := (abs_le.mp hx).2
  have hy : 0 ≤ Y := sq_nonneg _
  have hyV : Y ≤ V := by
    have hn := Complex.sq_norm u
    simp only [Complex.normSq_apply] at hn
    dsimp [Y,V,x]
    nlinarith [norm_nonneg u]
  let B := -(20/209:ℝ)+(96/5643)*x-(24/16929)*x^2
  have hB : B+(4/16929)*(Y+V) ≤ 0 := by
    dsimp [B,V] at *
    nlinarith [sq_nonneg x]
  have hd := mul_nonneg (sub_nonneg.mpr hyV) (neg_nonneg.mpr hB)
  have he : (fifthSepticRadicand u).re =
      1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4+B*Y+(4/16929)*Y^2 := by
    dsimp [fifthSepticRadicand,x,Y,B]
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have hbase :
      0 < 1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4+B*V+(4/16929)*V^2 := by
    have hx3 := mul_nonneg (sub_nonneg.mpr hxhi) (sq_nonneg x)
    have hsq := sq_nonneg (x-149/82)
    have hx4 := sq_nonneg (x^2)
    dsimp [B,V]
    nlinarith
  rw [he]
  nlinarith

theorem fifth_septic_slit (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    fifthSepticRadicand u ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (fifth_septic_radicand_positive u hu))

theorem fifth_septic_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u ≠ 0 ∧
      ‖(Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u)⁻¹‖ ≤ 4 := by
  have hs : 0 ≤ (Complex.sqrt (fifthSepticRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp := fifth_septic_poly_bound u hu
  have hr := Complex.re_le_norm (1-fifthSepticPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd := Complex.re_le_norm (Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/4:ℝ) ≤ ‖Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/4) hl
  norm_num at hi
  exact hi
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticTail

set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_septic_tail_norm (w : ℂ) (hw : ‖w‖ ≤ 3/2) : ‖fifthSepticTail w‖ ≤ 1/1000000 := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0 < (3*Real.sqrt 209/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 209/4:ℝ) ≤ 11 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
    have hp := Real.sqrt_nonneg 209
    nlinarith
  have ht := fifth_septic_residual_bound (w^2) hu
  have hd := (fifth_septic_denominator_bound (w^2) hu).2
  calc
    _ = (3*Real.sqrt 209/4:ℝ)*‖w‖^47*‖fifthSepticResidual (w^2)‖*
        ‖(Complex.sqrt (fifthSepticRadicand (w^2))+fifthSepticPoly (w^2))⁻¹‖ := by
      simp only [fifthSepticTail,div_eq_mul_inv,norm_mul,norm_neg,norm_pow,Complex.norm_real,
        Real.norm_eq_abs]
      norm_num [abs_of_nonneg (Real.sqrt_nonneg 209)]
    _ ≤ (11:ℝ)*(3/2)^47*(1/10000000000000000)*4 := by gcongr
    _ ≤ 1/1000000 := by norm_num

theorem fifth_septic_tail_differentiableAt (w : ℂ) (hw : ‖w‖ ≤ 3/2) :
    DifferentiableAt ℂ fifthSepticTail w := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => fifthSepticRadicand (v^2)) w := by
    unfold fifthSepticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (fifthSepticRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (fifth_septic_slit (w^2) hu)).comp w hh
  have hp : DifferentiableAt ℂ (fun v : ℂ => fifthSepticPoly (v^2)) w := by
    unfold fifthSepticPoly
    fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => fifthSepticResidual (v^2)) w := by
    unfold fifthSepticResidual
    fun_prop
  have hd := (fifth_septic_denominator_bound (w^2) hu).1
  unfold fifthSepticTail
  fun_prop

theorem fifth_septic_tail_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthSepticTail w‖ ≤ 1/25000 := by
  have hw' : ‖w‖ ≤ 29/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/20:ℝ), ‖u‖ ≤ 3/2 := by
    intro u hu
    have hd : ‖u-w‖ < 1/20 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ fifthSepticTail (Metric.ball w (1/20:ℝ)) := by
    intro u hu
    exact (fifth_septic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo fifthSepticTail (Metric.ball w (1/20:ℝ))
      (Metric.closedBall (fifthSepticTail w) (1/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := fifth_septic_tail_norm u (hball u hu)
    have h2 := fifth_septic_tail_norm w (by linarith)
    have hn := norm_sub_le (fifthSepticTail u) (fifthSepticTail w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/20)
  norm_num at hh
  exact hh
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators







theorem fifth_septic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt fifthSepticPolynomialError
      (-((3*Real.sqrt 209/4:ℝ):ℂ)*(∑ i : Fin 22,
        (fifthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2))) w := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (fifthSepticErrorCoeffs i:ℂ)

theorem fifth_septic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthSepticPolynomialError w‖ ≤ 559/10000 := by
  have hk : 0 < (3*Real.sqrt 209/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 209/4:ℝ) ≤ 10843/1000 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
    have hp := Real.sqrt_nonneg 209
    nlinarith
  rw [(fifth_septic_polynomial_error_hasDerivAt w).deriv]
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have hsum : ‖∑ i : Fin 22, (fifthSepticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(2:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    gcongr
  calc
    _ ≤ (10843/1000:ℝ)*(∑ i : Fin 22, |fifthSepticErrorCoeffs i| * ((2*i.val+3:ℕ):ℝ)*(2:ℝ)^(i.val+1)) :=
      mul_le_mul hku hsum (norm_nonneg _) (by norm_num)
    _ ≤ 559/10000 := by norm_num [fifthSepticErrorCoeffs,Fin.sum_univ_succ]

theorem fifth_septic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    DifferentiableAt ℂ fifthSepticError w := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  exact (fifth_septic_polynomial_error_hasDerivAt w).differentiableAt.add (fifth_septic_tail_differentiableAt w hn)

theorem fifth_septic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthSepticError w‖ ≤ 7/125 := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  have hp := fifth_septic_polynomial_error_deriv_bound w hw
  have ht := fifth_septic_tail_deriv_bound w hw
  have hd : deriv fifthSepticError w = deriv fifthSepticPolynomialError w+deriv fifthSepticTail w := by
    exact deriv_add (fifth_septic_polynomial_error_hasDerivAt w).differentiableAt (fifth_septic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv fifthSepticPolynomialError w) (deriv fifthSepticTail w)
  linarith











end DerivativeChainPrivate

end


section
-- Source module: FifthSepticAxes

set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem fifth_septic_radicand_real (x : ℝ) : fifthSepticRadicand (x:ℂ) =
    ((1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4:ℝ):ℂ) := by
  simp [fifthSepticRadicand]
theorem fifth_septic_poly_real (x : ℝ) : fifthSepticPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 24, fifthSepticCoeffs i*x^i.val):ℝ):ℂ) := by
  simp [fifthSepticPoly]
theorem fifth_septic_residual_real (x : ℝ) : fifthSepticResidual (x:ℂ) =
    ((∑ i : Fin 24, fifthSepticResidualCoeffs i*x^i.val : ℝ):ℂ) := by
  simp [fifthSepticResidual]
theorem fifth_septic_sqrt_real (x : ℝ) (hx : |x| ≤ 9/4) : Complex.sqrt (fifthSepticRadicand (x:ℂ)) =
    ((Real.sqrt (1-(32/57)*x+(20/209)*x^2-(32/5643)*x^3+(4/16929)*x^4):ℝ):ℂ) := by
  have hp := fifth_septic_radicand_positive (x:ℂ) (by simpa using hx)
  rw [fifth_septic_radicand_real,Complex.ofReal_re] at hp
  rw [fifth_septic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),Complex.ofReal_re]

theorem fifth_septic_tail_real_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthSepticTail (x:ℂ)).im = 0 := by
  unfold fifthSepticTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [fifth_septic_sqrt_real _ (by rw [abs_of_nonneg (sq_nonneg x)]; linarith),fifth_septic_poly_real,fifth_septic_residual_real]
  rw [← Complex.ofReal_pow]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,Complex.ofReal_im]

theorem fifth_septic_tail_imaginary_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthSepticTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold fifthSepticTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [fifth_septic_sqrt_real _ (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith),fifth_septic_poly_real,fifth_septic_residual_real]
  have he : (Complex.I*(x:ℂ))^47 = -Complex.I*((x^47:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod]
    norm_num [Complex.I_pow_three]
  rw [he]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div]
  simp only [Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,
    mul_one,one_mul,neg_zero,zero_div]

theorem fifth_septic_error_axes (x : ℝ) (hx : x^2 ≤ 2) :
    (fifthSepticError (x:ℂ)).im = 0 ∧ (fifthSepticError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [fifthSepticError,Complex.add_im,fifth_septic_tail_real_axis x hx,add_zero]
    norm_num [fifthSepticPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [fifthSepticError,Complex.add_re,fifth_septic_tail_imaginary_axis x hx,add_zero]
    norm_num [fifthSepticPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]
end DerivativeChainPrivate

end


section
-- Source module: AnalyticErrorCoordinates


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem analytic_error_coordinate_bounds (E : ℂ → ℂ) (R δ : ℝ)
    (hdiff : ∀ v : ℂ, ‖v‖^2 ≤ R → DifferentiableAt ℂ E v)
    (hderiv : ∀ v : ℂ, ‖v‖^2 ≤ R → ‖deriv E v‖ ≤ δ)
    (haxes : ∀ x : ℝ, x^2 ≤ R → (E (x:ℂ)).im=0 ∧ (E (Complex.I*(x:ℂ))).re=0)
    (w : ℂ) (hw : ‖w‖^2 ≤ R) :
    |(E w).re| ≤ (δ)*|w.re| ∧
      |(E w).im| ≤ (δ)*|w.im| := by
  let S := Metric.closedBall (0:ℂ) ‖w‖
  have hs (v : ℂ) (hv : v ∈ S) : ‖v‖^2 ≤ R := by
    have hn : ‖v‖ ≤ ‖w‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hw
  have hd : ∀ v ∈ S, DifferentiableAt ℂ E v := fun v hv => hdiff v (hs v hv)
  have hb : ∀ v ∈ S, ‖deriv E v‖ ≤ δ := fun v hv => hderiv v (hs v hv)
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
    have hp := Complex.abs_re_le_norm (E w-E (Complex.I*(w.im:ℂ)))
    rw [Complex.sub_re,(haxes w.im (by have hh := hw; rw [Complex.sq_norm,Complex.normSq_apply] at hh; nlinarith [sq_nonneg w.re])).2,sub_zero] at hp
    exact hp.trans hh
  · have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb hc hxr hwm
    have he : w-(w.re:ℂ) = Complex.I*(w.im:ℂ) := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    have hp := Complex.abs_im_le_norm (E w-E (w.re:ℂ))
    rw [Complex.sub_im,(haxes w.re (by have hh := hw; rw [Complex.sq_norm,Complex.normSq_apply] at hh; nlinarith [sq_nonneg w.im])).1,sub_zero] at hp
    exact hp.trans hh

end DerivativeChainPrivate

end


section
-- Source module: FifthSepticInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators



theorem fifth_septic_sqrt_exact_remainder (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    Complex.sqrt (fifthSepticRadicand u) = fifthSepticPoly u+
      u^25*fifthSepticResidual u/(Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u) := by
  have hd := (fifth_septic_denominator_bound u hu).1
  have hs : (Complex.sqrt (fifthSepticRadicand u))^2 = fifthSepticRadicand u :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have he : (Complex.sqrt (fifthSepticRadicand u)-fifthSepticPoly u)*
      (Complex.sqrt (fifthSepticRadicand u)+fifthSepticPoly u) = u^25*fifthSepticResidual u := by
    calc
      _ = (Complex.sqrt (fifthSepticRadicand u))^2-(fifthSepticPoly u)^2 := by ring
      _ = _ := by rw [hs,fifth_septic_remainder_identity]
  have hh := (eq_div_iff hd).mpr he
  linear_combination hh

theorem fifth_septic_polynomial_error_identity (w : ℂ) :
    w^3*((fifthSepticLeadingError:ℂ)*w+fifthSepticPolynomialError w) =
      (1/6)*w^4-((3*Real.sqrt 209/4:ℝ):ℂ)*
        (fifthSepticPoly (w^2)-1+(16/57)*w^2) := by
  norm_num [fifthSepticLeadingError,fifthSepticPolynomialError,fifthSepticPoly,fifthSepticErrorCoeffs,
    fifthSepticCoeffs,Fin.sum_univ_succ]
  push_cast
  ring

theorem fifth_septic_tail_identity (w : ℂ) (hw : ‖w^2‖ ≤ 9/4) :
    w^3*fifthSepticTail w = -((3*Real.sqrt 209/4:ℝ):ℂ)*
      (Complex.sqrt (fifthSepticRadicand (w^2))-fifthSepticPoly (w^2)) := by
  have hs := fifth_septic_sqrt_exact_remainder (w^2) hw
  have he : Complex.sqrt (fifthSepticRadicand (w^2))-fifthSepticPoly (w^2) =
      (w^2)^25*fifthSepticResidual (w^2)/(Complex.sqrt (fifthSepticRadicand (w^2))+fifthSepticPoly (w^2)) := by
    linear_combination hs
  rw [he]
  dsimp only [fifthSepticTail]
  ring

theorem fifth_septic_remainder_exact (z : ℂ) (hz : z ≠ 0) (hn : ‖z⁻¹‖^2 ≤ 2) :
    fifthSepticRemainder z = (1/6)/z-((3*Real.sqrt 209/4:ℝ):ℂ)*z^3*
      (Complex.sqrt (fifthSepticRadicand ((z⁻¹)^2))-1+(16/57)*(z⁻¹)^2) := by
  have hw : ‖(z⁻¹)^2‖ ≤ 9/4 := by rw [norm_pow]; linarith
  have hP := fifth_septic_polynomial_error_identity z⁻¹
  have hT := fifth_septic_tail_identity z⁻¹ hw
  have hR : (z⁻¹)^3*fifthSepticRemainder z = (1/6)*(z⁻¹)^4-
      ((3*Real.sqrt 209/4:ℝ):ℂ)*(Complex.sqrt (fifthSepticRadicand ((z⁻¹)^2))-1+(16/57)*(z⁻¹)^2) := by
    dsimp only [fifthSepticRemainder,fifthSepticError]
    linear_combination hP+hT
  apply mul_left_cancel₀ (pow_ne_zero 3 (inv_ne_zero hz))
  rw [hR]
  field_simp <;> ring

theorem fifth_septic_inverse_exact (z : ℂ) (hz : z ≠ 0) (hn : ‖z⁻¹‖^2 ≤ 2) :
    (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z =
      (55/4)*z^2-5+(1/6)/z^2-((3*Real.sqrt 209/4:ℝ):ℂ)*z^2*
        Complex.sqrt (fifthSepticRadicand ((z⁻¹)^2)) := by
  rw [fifth_septic_remainder_exact z hz hn]
  push_cast
  field_simp <;> ring
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticGraphs

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_upper_graphs (β z : ℂ) (hx : 0 < z.re) (hX : 1/2 ≤ z.re^2)
    (hroot : (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
      z^7-z^5+(10/39)*z^3-(2/143)*z=0) :
    β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z ∨
    β/z = (((55+3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5+4*Real.sqrt 209/19:ℝ):ℂ)+
      ((1/3)/z-fifthSepticRemainder z)/z := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hnorm : 1/2 ≤ ‖z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hn : ‖z⁻¹‖^2 ≤ 2 := by
    rw [norm_inv,inv_pow]
    apply (inv_le_comm₀ (by positivity : 0 < ‖z‖^2) (by norm_num)).mpr
    norm_num
    exact hnorm
  let S := Complex.sqrt (fifthSepticRadicand ((z⁻¹)^2))
  let s : ℂ := (Real.sqrt 209:ℂ)
  have hs : s^2 = 209 := by
    dsimp [s]
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hS : S^2 = fifthSepticRadicand ((z⁻¹)^2) := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hd : (β*z-(55/4)*z^4+5*z^2-1/6)^2 =
      (1881/16)*(z^8-(32/57)*z^6+(20/209)*z^4-(32/5643)*z^2+4/16929) := by
    linear_combination (143/2)*z*hroot
  have hsquare : ((3/4)*s*z^4*S)^2 =
      (1881/16)*(z^8-(32/57)*z^6+(20/209)*z^4-(32/5643)*z^2+4/16929) := by
    calc
      _ = (9/16)*s^2*z^8*S^2 := by ring
      _ = _ := by rw [hs,hS]; unfold fifthSepticRadicand; field_simp; ring
  have hsplit := (sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  have hbase : β/z = (55/4)*z^2-5+(1/6)/z^2-(3*s/4)*z^2*S ∨
      β/z = (55/4)*z^2-5+(1/6)/z^2+(3*s/4)*z^2*S := by
    rcases hsplit with hp|hm
    · right
      apply (div_eq_iff hz).mpr
      apply mul_left_cancel₀ hz
      have he : z*((55/4)*z^2-5+(1/6)/z^2+(3*s/4)*z^2*S)*z =
          (55/4)*z^4-5*z^2+1/6+(3/4)*s*z^4*S := by field_simp <;> ring
      rw [← mul_assoc,he]
      linear_combination hp
    · left
      apply (div_eq_iff hz).mpr
      apply mul_left_cancel₀ hz
      have he : z*((55/4)*z^2-5+(1/6)/z^2-(3*s/4)*z^2*S)*z =
          (55/4)*z^4-5*z^2+1/6-(3/4)*s*z^4*S := by field_simp <;> ring
      rw [← mul_assoc,he]
      linear_combination hm
  have hminus := fifth_septic_inverse_exact z hz hn
  change _ = (55/4)*z^2-5+(1/6)/z^2-((3*Real.sqrt 209/4:ℝ):ℂ)*z^2*S at hminus
  have hplus : (((55+3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5+4*Real.sqrt 209/19:ℝ):ℂ)+
      ((1/3)/z-fifthSepticRemainder z)/z =
      (55/4)*z^2-5+(1/6)/z^2+(3*s/4)*z^2*S := by
    calc
      _ = (55/2)*z^2-10+(1/3)/z^2-
          ((((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z) := by
        push_cast
        field_simp
        ring
      _ = _ := by rw [hminus]; dsimp only [s]; push_cast; ring
  rcases hbase with hm|hp
  · left
    rw [hminus]
    convert hm using 1 <;> dsimp only [s] <;> push_cast <;> ring
  · right
    rw [hplus]
    exact hp
end DerivativeChainPrivate

end


section
-- Source module: InverseErrorCoordinates

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_error_coordinate_bounds (E : ℂ → ℂ) (γ δ : ℝ) (z : ℂ)
    (hx : 0 < z.re) (hy : 0 < z.im)
    (herr : |(E z⁻¹).re| ≤ δ*|(z⁻¹).re| ∧ |(E z⁻¹).im| ≤ δ*|(z⁻¹).im|) :
    let e := (γ:ℂ)*z⁻¹+E z⁻¹
    let U := z.re^2+z.im^2
    (γ-δ)/U ≤ e.re/z.re ∧ e.re/z.re ≤ (γ+δ)/U ∧
      -(γ+δ)/U ≤ e.im/z.im ∧ e.im/z.im ≤ -(γ-δ)/U := by
  let U := z.re^2+z.im^2
  have hUp : 0 < U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUn : Complex.normSq z = U := by simp [U,Complex.normSq_apply,pow_two]
  obtain ⟨hr,hi⟩ := herr
  have hwr : (z⁻¹).re = z.re/U := by rw [Complex.inv_re,hUn]
  have hwi : (z⁻¹).im = -z.im/U := by rw [Complex.inv_im,hUn]
  rw [hwr,abs_of_pos (div_pos hx hUp)] at hr
  rw [hwi,abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hy) hUp)] at hi
  have hrlo := (abs_le.mp hr).1
  have hrhi := (abs_le.mp hr).2
  have hilo := (abs_le.mp hi).1
  have hihi := (abs_le.mp hi).2
  have hAr : ((γ:ℂ)*z⁻¹+E z⁻¹).re/z.re = γ/U+(E z⁻¹).re/z.re := by
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hwr]
    field_simp
  have hBi : ((γ:ℂ)*z⁻¹+E z⁻¹).im/z.im = -γ/U+(E z⁻¹).im/z.im := by
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,hwi]
    field_simp
  have herlo : -δ/U ≤ (E z⁻¹).re/z.re := by
    have hh := div_le_div_of_nonneg_right hrlo hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have herhi : (E z⁻¹).re/z.re ≤ δ/U := by
    have hh := div_le_div_of_nonneg_right hrhi hx.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heilo : -δ/U ≤ (E z⁻¹).im/z.im := by
    have hh := div_le_div_of_nonneg_right hilo hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  have heihi : (E z⁻¹).im/z.im ≤ δ/U := by
    have hh := div_le_div_of_nonneg_right hihi hy.le
    convert hh using 1 <;> first | rfl | (field_simp <;> ring)
  dsimp only
  change (γ-δ)/U ≤ _ ∧ _ ≤ (γ+δ)/U ∧ -(γ+δ)/U ≤ _ ∧ _ ≤ -(γ-δ)/U
  rw [hAr,hBi]
  simp only [sub_div,add_div,neg_div] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticCoordinates

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_leading_bounds : (3/40:ℝ) < fifthSepticLeadingError ∧ fifthSepticLeadingError < 151/2000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have hp := Real.sqrt_nonneg 209
  dsimp only [fifthSepticLeadingError]
  constructor <;> nlinarith

theorem fifth_septic_error_coordinates (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    |(fifthSepticError w).re| ≤ (7/125)*|w.re| ∧ |(fifthSepticError w).im| ≤ (7/125)*|w.im| :=
  analytic_error_coordinate_bounds fifthSepticError 2 (7/125)
    fifth_septic_error_differentiableAt fifth_septic_error_deriv_bound fifth_septic_error_axes w hw





theorem fifth_septic_remainder_bounds (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 1/2 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    0 < (fifthSepticRemainder z).re/z.re ∧ (fifthSepticRemainder z).re/z.re ≤ (263/2000)/U ∧
      -(263/2000)/U ≤ (fifthSepticRemainder z).im/z.im ∧ (fifthSepticRemainder z).im/z.im < 0 := by
  have hU : 1/2 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < z.re^2+z.im^2 := by linarith
  have hn : ‖z⁻¹‖^2 ≤ 2 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by nlinarith) (by norm_num)).mpr
    norm_num
    nlinarith
  obtain ⟨hAlo,hAhi,hBlo,hBhi⟩ := inverse_error_coordinate_bounds fifthSepticError fifthSepticLeadingError
    (7/125) z hx hy (fifth_septic_error_coordinates z⁻¹ hn)
  obtain ⟨hgl,hgu⟩ := fifth_septic_leading_bounds
  have hp : 0 < (fifthSepticLeadingError-7/125)/(z.re^2+z.im^2) := div_pos (by linarith) hUp
  have hu : (fifthSepticLeadingError+7/125)/(z.re^2+z.im^2) ≤ (263/2000)/(z.re^2+z.im^2) :=
    div_le_div_of_nonneg_right (by linarith) hUp.le
  change 0 < _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ < _
  change (fifthSepticLeadingError-7/125)/_ ≤ (fifthSepticRemainder z).re/z.re at hAlo
  change (fifthSepticRemainder z).re/z.re ≤ _ at hAhi
  change _ ≤ (fifthSepticRemainder z).im/z.im at hBlo
  change (fifthSepticRemainder z).im/z.im ≤ _ at hBhi
  simp only [neg_div] at hBlo hBhi ⊢
  exact ⟨lt_of_lt_of_le hp hAlo,hAhi.trans hu,by linarith,by linarith⟩
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticScalars

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_scalar_gaps :
    (29/10:ℝ) < (55-3*Real.sqrt 209)/4 ∧ (55-3*Real.sqrt 209)/4 < 3 ∧
    (12/5:ℝ) < 55-3*Real.sqrt 1122/2 ∧ (55-3*Real.sqrt 209)/4 < 55-3*Real.sqrt 1122/2 ∧
    (5/8:ℝ) < (10-15*Real.sqrt 1122/68)-(5-4*Real.sqrt 209/19) ∧
    (263/1000:ℝ) < (5-4*Real.sqrt 209/19)-(29/50)*((55-3*Real.sqrt 209)/4) ∧
    (237/1160:ℝ) < (5-4*Real.sqrt 209/19)-(3/5)*((55-3*Real.sqrt 209)/4) ∧
    (24:ℝ) < (55+3*Real.sqrt 209)/4 ∧ (5+4*Real.sqrt 209/19) < 9 := by
  have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have p1 := Real.sqrt_nonneg 209
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1122)
  have p2 := Real.sqrt_nonneg 1122
  have l1 : (144568:ℝ)/10000 < Real.sqrt 209 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 209 < (144569:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (334962:ℝ)/10000 < Real.sqrt 1122 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 1122 < (334963:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

end


section
-- Source module: FifthSepticUpperData


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_upper_data (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 1/2 ≤ z.re^2)
    (hroot : (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
      z^7-z^5+(10/39)*z^3-(2/143)*z=0) :
    ∃ α b : ℝ, ∃ e : ℂ, 29/10 < α ∧ β/z = (α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((α = (55-3*Real.sqrt 209)/4 ∧ b = 5-4*Real.sqrt 209/19 ∧ e = fifthSepticRemainder z ∧
          0 ≤ (3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α = (55+3*Real.sqrt 209)/4 ∧ b = 5+4*Real.sqrt 209/19 ∧
          0 ≤ e.re/z.re ∧ e.re/z.re ≤ 2/3 ∧ -(2/3) ≤ e.im/z.im ∧ e.im/z.im ≤ 0)) := by
  obtain ⟨hAp,hAr,hBr,hBn⟩ := fifth_septic_remainder_bounds z hx hy hX
  obtain ⟨hαm,hαm3,_,_,_,_,_,hαp,_⟩ := fifth_septic_scalar_gaps
  have hU : 1/2 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < z.re^2+z.im^2 := by linarith
  have hsmall : (263/2000:ℝ)/(z.re^2+z.im^2) ≤ 263/1000 := by
    apply (div_le_iff₀ hUp).mpr
    linarith
  have hAu : (fifthSepticRemainder z).re/z.re ≤ 263/1000 := hAr.trans hsmall
  have hBl : -(263/1000) ≤ (fifthSepticRemainder z).im/z.im := by
    rw [neg_div] at hBr
    linarith only [hBr,hsmall]
  have hCp : 0 < (3*((fifthSepticRemainder z).re/z.re)-(fifthSepticRemainder z).im/z.im)/2 := by linarith
  rcases fifth_septic_upper_graphs β z hx hX hroot with hm|hp
  · refine ⟨(55-3*Real.sqrt 209)/4,5-4*Real.sqrt 209/19,fifthSepticRemainder z,hαm,hm,?_,
      Or.inl ⟨rfl,rfl,rfl,hCp.le⟩⟩
    exact cubic_graph_positive_phase_general β z (fifthSepticRemainder z) _ _ (263/1000) (1/2)
      hx hy hX (by norm_num) (by linarith) (by linarith) hAu hBl hm
  · let E := (1/3:ℂ)/z-fifthSepticRemainder z
    let U := z.re^2+z.im^2
    have hU : 1/2 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
    have hUp : 0 < U := by linarith
    have hUn : Complex.normSq z = U := by simp [U,Complex.normSq_apply,pow_two]
    have hArat : ((1/3:ℂ)/z).re/z.re = (1/3:ℝ)/U := by
      rw [div_eq_mul_inv]
      simp only [Complex.mul_re,Complex.div_re,Complex.inv_re,Complex.inv_im,hUn]
      norm_num
      field_simp
    have hBrat : ((1/3:ℂ)/z).im/z.im = -(1/3:ℝ)/U := by
      rw [div_eq_mul_inv]
      simp only [Complex.mul_im,Complex.div_im,Complex.inv_re,Complex.inv_im,hUn]
      norm_num
      field_simp
    have hAe : E.re/z.re = (1/3:ℝ)/U-(fifthSepticRemainder z).re/z.re := by
      simp only [E,Complex.sub_re,sub_div,hArat]
    have hBe : E.im/z.im = -(1/3:ℝ)/U-(fifthSepticRemainder z).im/z.im := by
      simp only [E,Complex.sub_im,sub_div,hBrat]
    have hcompare : (263/2000:ℝ)/U ≤ (1/3:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hbound : (1/3:ℝ)/U ≤ 2/3 := by apply (div_le_iff₀ hUp).mpr; linarith
    change (fifthSepticRemainder z).re/z.re ≤ (263/2000:ℝ)/U at hAr
    change -(263/2000:ℝ)/U ≤ (fifthSepticRemainder z).im/z.im at hBr
    simp only [neg_div] at hBr hBe
    have hA0 : 0 ≤ E.re/z.re := by rw [hAe]; linarith
    have hA1 : E.re/z.re ≤ 2/3 := by rw [hAe]; linarith
    have hB0 : -(2/3) ≤ E.im/z.im := by rw [hBe]; linarith
    have hB1 : E.im/z.im ≤ 0 := by rw [hBe]; linarith
    refine ⟨(55+3*Real.sqrt 209)/4,5+4*Real.sqrt 209/19,E,by linarith,hp,?_,
      Or.inr ⟨rfl,rfl,hA0,hA1,hB0,hB1⟩⟩
    exact cubic_graph_positive_phase_general β z E _ _ (2/3) (1/2) hx hy hX
      (by norm_num) (by linarith) (by linarith) hA1 hB0 hp

end DerivativeChainPrivate

end


section
-- Source module: FifthSepticPhase

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_nonnegative_im (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 1/2 ≤ z.re^2)
    (hroot : (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
      z^7-z^5+(10/39)*z^3-(2/143)*z=0) :
    0 ≤ z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0 ≤ z.im := by
    by_contra hn
    have hy : z.im < 0 := lt_of_not_ge hn
    have hroot' : (2/143)*(starRingEnd ℂ β)^2*(starRingEnd ℂ z)-(5/13)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^4+
        (20/143)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^2-(2/429)*(starRingEnd ℂ β)+
        (starRingEnd ℂ z)^7-(starRingEnd ℂ z)^5+(10/39)*(starRingEnd ℂ z)^3-(2/143)*(starRingEnd ℂ z)=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_septic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
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
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_septic_upper_data β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    have hxn : (z.re:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hn : (z.re⁻¹)^2 ≤ 2 := by
      rw [inv_pow]
      exact (inv_le_comm₀ (sq_pos_of_pos hx) (by norm_num)).mpr (by norm_num; exact hX)
    have heIm : (fifthSepticRemainder (z.re:ℂ)).im=0 := by
      unfold fifthSepticRemainder
      rw [← Complex.ofReal_inv,Complex.add_im,(fifth_septic_error_axes _ hn).1]
      simp
    rcases fifth_septic_upper_graphs β (z.re:ℂ) (by simpa using hx) (by simpa using hX) hroot with hm|hp
    · have hi := congrArg Complex.im hm
      simp [Complex.div_im,heIm,← Complex.ofReal_pow] at hi
      exact hi.resolve_right hx.ne'
    · have hi := congrArg Complex.im hp
      simp [Complex.div_im,heIm,← Complex.ofReal_pow] at hi
      exact hi.resolve_right hx.ne'

end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w E₀ : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 1/2 ≤ w.re^2)
    (hwroot : (2/1001)*β^2-(20/91)*β*w^3+(40/1001)*β*w+w^6-(5/7)*w^4+(10/91)*w^2-2/1001=0)
    (hwinv : β/w = ((55-3*Real.sqrt 1122/2:ℝ):ℂ)*w^2-((10-15*Real.sqrt 1122/68:ℝ):ℂ)+E₀/w)
    (hA₀hi : E₀.re/w.re ≤ 2821/12500) (hB₀hi : E₀.im/w.im ≤ 0)
    (hC₀hi : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 5/8)
    (hWedge : 1/2 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
        z^7-z^5+(10/39)*z^3-(2/143)*z=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧
      β/z = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*z^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder z/z := by
  let α₀ := 55-3*Real.sqrt 1122/2
  let b₀ := 10-15*Real.sqrt 1122/68
  obtain ⟨hαm,_,_,hαm6,hgap,_,_,hαp,hbfast⟩ := fifth_septic_scalar_gaps
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1122)
  have hp := Real.sqrt_nonneg 1122
  have hα₀ : 0 < α₀ := by dsimp [α₀]; nlinarith only [hs,hp]
  have hα₀up : α₀ < 5 := by dsimp [α₀]; nlinarith only [hs,hp]
  have hb₀lo : (5/2:ℝ) < b₀ := by dsimp [b₀]; nlinarith only [hs,hp]
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  obtain ⟨hr₀,hi₀,_⟩ := cubic_graph_coordinate_parts β w E₀ α₀ b₀ hw hwinv
  have hR₀ : β.re/w.re = α₀*(w.re^2-3*w.im^2)-b₀+E₀.re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im = α₀*(3*w.re^2-w.im^2)-b₀+E₀.im/w.im := by rw [hi₀]; field_simp
  let p : Polynomial ℂ := X^7-X^5-C ((5/13)*β)*X^4+C (10/39)*X^3+
    C ((20/143)*β)*X^2+C ((2/143)*β^2-2/143)*X-C ((2/429)*β)
  have hpdeg : p.natDegree = 7 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w=0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 7*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 1/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hzroot : (2/143)*β^2*z-(5/13)*β*z^4+(20/143)*β*z^2-(2/429)*β+
      z^7-z^5+(10/39)*z^3-(2/143)*z=0 := by
    have he := hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at he
    linear_combination he
  obtain ⟨hy0,hzero⟩ := fifth_septic_nonnegative_im β z hR hI.le hx hX hzroot
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fifth_septic_upper_data β z hx hy hX hzroot
  obtain ⟨hr₁,hi₁,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  have hslow : α = (55-3*Real.sqrt 209)/4 ∧ b = 5-4*Real.sqrt 209/19 ∧ e=fifthSepticRemainder z ∧
      0 ≤ (3*(e.re/z.re)-e.im/z.im)/2 := by
    rcases hcases with hs|⟨ha,hb,hAlo,hAhi,hBlo,hBhi⟩
    · exact hs
    · exfalso
      subst α
      subst b
      by_cases hvy : z.im ≤ w.im
      · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ _ b₀ _
          (E₀.re/w.re) (e.re/z.re) (1/2) (2821/12500) 0 hR hwpos hy.le hxz hvy hWedge
          (by linarith) (by linarith only [hαp,hα₀up]) hA₀hi hAlo (by dsimp [α₀,b₀] at *; linarith only [hαp,hα₀up,hb₀lo,hbfast]) hR₀ hR₁
      · exact fast_graph_northeast_impossible α₀ _ b₀ _ (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
          (1/2) (8/9) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
          hR hI.le hwX hα₀.le (by linarith) (by linarith) hB₀hi (by linarith) (by dsimp [α₀,b₀] at *; linarith only [hαp,hα₀up,hb₀lo,hbfast]) hI₀ hR₁ hI₁
  rcases hslow with ⟨rfl,rfl,rfl,hC₁⟩
  have himorder : w.im ≤ z.im := by
    by_contra hn
    have hvy := le_of_not_ge hn
    exact inverse_graph_southeast_impossible α₀ _ b₀ _ (E₀.re/w.re) ((fifthSepticRemainder z).re/z.re)
      (E₀.im/w.im) ((fifthSepticRemainder z).im/z.im) (5/8) β.re β.im w.re w.im z.re z.im
      (by linarith) hαm6 hwpos hy hxz hvy hR hI.le hC₀hi hC₁ hgap hR₀ hI₀ hR₁ hI₁
  exact ⟨z,hzroot,hxz,himorder,hgraph⟩
