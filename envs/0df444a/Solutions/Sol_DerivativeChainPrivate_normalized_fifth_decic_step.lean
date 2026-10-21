-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_decic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T22:42:11.357987+00:00
-- url     : https://prove2.me/submissions/b7bc5ace-1aaf-4fd7-bcf4-c815f0f291e6

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Definitions.Def_DerivativeChainPrivate_fifth_row10_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_complete_inverse_branches
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
-- Source module: FifthSepticLocalization

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_norm_square_bound (z : ℂ) (T : ℝ) (hT : 0 < T) (hX : T ≤ z.re^2) :
    ‖z⁻¹‖^2 ≤ T⁻¹ := by
  have hnorm : T ≤ ‖z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  rw [norm_inv,inv_pow]
  exact inv_anti₀ hT hnorm


end DerivativeChainPrivate

end


section
-- Source module: FifthUnitRows

set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial


 

 theorem fifth_unit_p10_degree (β : ℂ) : (fifthUnitP10 β).natDegree=10 := by
  unfold fifthUnitP10
  compute_degree <;> norm_num





end DerivativeChainPrivate

end


section
-- Source module: NewtonTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



theorem newton_tail_norm (Y : ℂ → ℂ)
    (hY : ∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000)
    (w : ℂ) (hw : ‖w‖ ≤ 7/5) : ‖newtonTail Y w‖ ≤ 1/100000 := by
  have hu : ‖w^2‖ ≤ 2 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  dsimp [newtonTail]
  rw [norm_mul,norm_pow]
  calc
    _ ≤ (7/5:ℝ)^61*(1/100000000000000) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw 61) (hY _ hu) (norm_nonneg _) (by positivity)
    _ ≤ _ := by norm_num

theorem newton_tail_differentiableAt (Y : ℂ → ℂ)
    (hY : DifferentiableOn ℂ Y (Metric.ball 0 2))
    (w : ℂ) (hw : ‖w‖ ≤ 7/5) : DifferentiableAt ℂ (newtonTail Y) w := by
  have hu : w^2 ∈ Metric.ball (0:ℂ) 2 := by
    rw [Metric.mem_ball,dist_zero_right,norm_pow]
    nlinarith [norm_nonneg w]
  have hy := hY.differentiableAt (Metric.isOpen_ball.mem_nhds hu)
  have hc : DifferentiableAt ℂ (fun v : ℂ => Y (v^2)) w := by
    exact hy.comp w (differentiableAt_id.pow 2)
  exact (differentiableAt_id.pow 61).mul hc

theorem newton_tail_deriv_bound (Y : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ Y (Metric.ball 0 2))
    (hY : ∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000)
    (w : ℂ) (hw : ‖w‖^2 ≤ 10/7) : ‖deriv (newtonTail Y) w‖ ≤ 1/10000 := by
  have hw' : ‖w‖ ≤ 6/5 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/5:ℝ), ‖u‖ ≤ 7/5 := by
    intro u hu
    have hd : ‖u-w‖ < 1/5 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ (newtonTail Y) (Metric.ball w (1/5:ℝ)) := by
    intro u hu
    exact (newton_tail_differentiableAt Y hhol u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo (newtonTail Y) (Metric.ball w (1/5:ℝ))
      (Metric.closedBall (newtonTail Y w) (1/50000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := newton_tail_norm Y hY u (hball u hu)
    have h2 := newton_tail_norm Y hY w (by linarith)
    have hn := norm_sub_le (newtonTail Y u) (newtonTail Y w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/5)
  norm_num at hh
  exact hh

theorem newton_tail_axes (Y : ℂ → ℂ)
    (hY : ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0)
    (x : ℝ) (hx : x^2 ≤ 10/7) :
    (newtonTail Y (x:ℂ)).im=0 ∧ (newtonTail Y (Complex.I*(x:ℂ))).re=0 := by
  have hpos := hY (x^2) (by rw [abs_of_nonneg (sq_nonneg x)]; linarith)
  have hneg := hY (-x^2) (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith)
  constructor
  · dsimp [newtonTail]
    rw [← Complex.ofReal_pow,← Complex.ofReal_pow]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hpos,mul_zero,zero_mul,add_zero]
  · dsimp [newtonTail]
    rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
    have he : (Complex.I*(x:ℂ))^61 = Complex.I*((x^61:ℝ):ℂ) := by norm_num [mul_pow,Complex.I_pow_eq_pow_mod]
    rw [he]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,hneg,mul_zero,zero_mul,add_zero,zero_add,sub_zero,zero_sub,mul_one,one_mul,neg_zero]
end DerivativeChainPrivate

end


section
-- Source module: QuadraticIntervalBound

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem quadratic_midpoint_bound (α m ε a b c : ℝ) (hα : |α-m| ≤ ε) :
    |a+b*α+c*α^2| ≤ |a+b*m+c*m^2|+ε*(|b+2*c*m|+|c| *ε) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hα
  have he : a+b*α+c*α^2 = (a+b*m+c*m^2)+(α-m)*(b+2*c*m)+c*(α-m)^2 := by ring
  rw [he]
  calc
    _ ≤ |a+b*m+c*m^2|+|(α-m)*(b+2*c*m)|+|c*(α-m)^2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |a+b*m+c*m^2|+ε*|b+2*c*m|+|c| *ε^2 := by
      simp only [abs_mul,abs_pow]
      gcongr
    _ = _ := by ring
end DerivativeChainPrivate

end


section
-- Source module: FifthCubicRows

set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



theorem fifth_decic_inverse_equation (β z : ℂ) (hz : z ≠ 0) (hroot : (fifthUnitP10 β).eval z=0) :
    row10G0 ((z⁻¹)^2)+row10G1 ((z⁻¹)^2)*(β/z^3)+row10G2 ((z⁻¹)^2)*(β/z^3)^2-60*(β/z^3)^3=0 := by
  have he : z^10*(row10G0 ((z⁻¹)^2)+row10G1 ((z⁻¹)^2)*(β/z^3)+row10G2 ((z⁻¹)^2)*(β/z^3)^2-60*(β/z^3)^3)=
      3003*(fifthUnitP10 β).eval z := by
    simp only [fifthUnitP10,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    dsimp [row10G0,row10G1,row10G2]
    field_simp <;> ring
  rw [hroot,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 10 hz)



theorem fifth_decic_derivative (β w : ℂ) :
    (fifthUnitP10 β).derivative.eval w=10*(fifthUnitP9 β).eval w := by
  norm_num [fifthUnitP10,fifthUnitP9,derivative_add,derivative_mul,derivative_pow,derivative_X,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  ring


end DerivativeChainPrivate

end


section
-- Source module: Row10BoundP1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_p_coefficient_bounds_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row10PCoeffs α i| ≤ row10PBounds1 i := by
  have hm : |α-(92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10PCoeffs,row10PBounds1]
    apply (quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num


end DerivativeChainPrivate

end


section
-- Source module: Row10BoundP2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_p_coefficient_bounds_2 (α : ℝ)
    (hlo : (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    ∀ i : Fin 32, |row10PCoeffs α i| ≤ row10PBounds2 i := by
  have hm : |α-(194321947296730718601147848629408529324060800528524268971722372112766700316491983402861459659286240459025588037238647/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10PCoeffs,row10PBounds2]
    apply (quadratic_midpoint_bound α (194321947296730718601147848629408529324060800528524268971722372112766700316491983402861459659286240459025588037238647/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num


end DerivativeChainPrivate

end


section
-- Source module: Row10BoundP3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_p_coefficient_bounds_3 (α : ℝ)
    (hlo : (342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row10PCoeffs α i| ≤ row10PBounds3 i := by
  have hm : |α-(1368454411899111887120711722121899420795960997849082462032048820866607474609986219561800811974020489811926885335168181/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10PCoeffs,row10PBounds3]
    apply (quadratic_midpoint_bound α (1368454411899111887120711722121899420795960997849082462032048820866607474609986219561800811974020489811926885335168181/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num


end DerivativeChainPrivate

end


section
-- Source module: Row10Estimates1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_branch_estimates_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    (1461/1250:ℝ) < α ∧ α < (11689/10000:ℝ) ∧
    (2229/2000:ℝ) < -row10PCoeffs α 1 ∧ -row10PCoeffs α 1 < (5573/5000:ℝ) ∧
    (1/50:ℝ) < row10PCoeffs α 2 ∧ row10PCoeffs α 2 < (21/1000:ℝ) ∧
    (∑ i : Fin 29, |row10PCoeffs α ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*(5/4:ℝ)^(i.val+1)) ≤ (1/500:ℝ)-1/10000 := by
  have hm : |α-(92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by rw [abs_le]; constructor <;> linarith only [hlo,hhi]
  have h1 := quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (599805995828873252946884609578139564668879924918856621206888308657939900854559499099518717378692676253985084536792954181323753973520848520744613614461750272235470740750018778527550875734948229447418955722888538059554680354946215499425/843017324119284951785895862235138887504489107294366259848505256648145667308702649277666975993955037527114837768542172750951167963954344214554247990347361358588019051979321498713794050097957955540117808562188042531734815841622119415808) (-1015/1629) (20/1629) hm
  have he1 : (599805995828873252946884609578139564668879924918856621206888308657939900854559499099518717378692676253985084536792954181323753973520848520744613614461750272235470740750018778527550875734948229447418955722888538059554680354946215499425/843017324119284951785895862235138887504489107294366259848505256648145667308702649277666975993955037527114837768542172750951167963954344214554247990347361358588019051979321498713794050097957955540117808562188042531734815841622119415808:ℝ)+(-1015/1629)*α+(20/1629)*α^2=row10PCoeffs α 1-(-2818646115082035174765958862910051621532785444993681188833452588937922153002284923174777827532084441536450448813045412103822904219523921210217015439449786234594136914007744298576401787221989067370042026139340475913625195024368888480739/2529051972357854855357687586705416662513467321883098779545515769944437001926107947833000927981865112581344513305626518252853503891863032643662743971042084075764057155937964496141382150293873866620353425686564127595204447524866358247424) := by
    dsimp [row10PCoeffs]
    ring
  rw [he1] at h1
  norm_num at h1
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have h2 := quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (-159354290358258034389250070889500552594171200988492196157110744839075840095064862375266219041070073844085651904825307174043968748382593691267686755862585742366027858506508312620789615192701171927638203557406157734563489014954443217894275/2237929989761995118674291548946882033361917083497444297811165287981944031482169299615779932271952639621980855996223287929525033888310799108236676998375461953264994576654438805252218604993379052640499409129755190240912024454226186342498304) (617795/9730017) (-21415/9730017) hm
  have he2 : (-159354290358258034389250070889500552594171200988492196157110744839075840095064862375266219041070073844085651904825307174043968748382593691267686755862585742366027858506508312620789615192701171927638203557406157734563489014954443217894275/2237929989761995118674291548946882033361917083497444297811165287981944031482169299615779932271952639621980855996223287929525033888310799108236676998375461953264994576654438805252218604993379052640499409129755190240912024454226186342498304:ℝ)+(617795/9730017)*α+(-21415/9730017)*α^2=row10PCoeffs α 2-(1215225256287592538654621005301005413653668379278992181937648949732366705952716835220830448555427950445016799190507047259247939787443221535772649844568372148098494605450710276884250962665363711469823845327343301642251186364577646598588113/60424109723573868204205871821565814900771761254430996040901462775512488850018571089626058171342721269793483111898028774097175914984391575922390278956137472738154853569669847741809902334821234421293484046503390136504624660264107031247454208) := by
    dsimp [row10PCoeffs]
    ring
  rw [he2] at h2
  norm_num at h2
  have h2lo := (abs_le.mp h2).1
  have h2hi := (abs_le.mp h2).2
  refine ⟨by linarith only [hlo],by linarith only [hhi],by linarith only [h1lo,h1hi],
    by linarith only [h1lo,h1hi],by linarith only [h2lo,h2hi],by linarith only [h2lo,h2hi],?_⟩
  calc
    _ ≤ ∑ i : Fin 29, row10PBounds1 ⟨i.val+3,by omega⟩ * ((2*i.val+3:ℕ):ℝ)*(5/4:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact row10_p_coefficient_bounds_1 α hlo hhi _
    _ ≤ _ := by norm_num [row10PBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row10Estimates2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_branch_estimates_2 (α : ℝ)
    (hlo : (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    (12329/5000:ℝ) < α ∧ α < (24659/10000:ℝ) ∧
    (2331/1250:ℝ) < -row10PCoeffs α 1 ∧ -row10PCoeffs α 1 < (18649/10000:ℝ) ∧
    (23/250:ℝ) < row10PCoeffs α 2 ∧ row10PCoeffs α 2 < (93/1000:ℝ) ∧
    (∑ i : Fin 29, |row10PCoeffs α ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*(5/4:ℝ)^(i.val+1)) ≤ (41/1000:ℝ)-1/10000 := by
  have hm : |α-(194321947296730718601147848629408529324060800528524268971722372112766700316491983402861459659286240459025588037238647/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by rw [abs_le]; constructor <;> linarith only [hlo,hhi]
  have h1 := quadratic_midpoint_bound α (194321947296730718601147848629408529324060800528524268971722372112766700316491983402861459659286240459025588037238647/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (410773027668972758951188360823725732947481511599429460025732240589082293289910854043766073607254636049223657058926034223324562841406465330385660684953874700934407563518201187127845798495643133748434051308701907931965167905249919711955/281005774706428317261965287411712962501496369098122086616168418882715222436234216425888991997985012509038279256180724250317055987984781404851415996782453786196006350659773832904598016699319318513372602854062680843911605280540706471936) (-1015/1629) (20/1629) hm
  have he1 : (410773027668972758951188360823725732947481511599429460025732240589082293289910854043766073607254636049223657058926034223324562841406465330385660684953874700934407563518201187127845798495643133748434051308701907931965167905249919711955/281005774706428317261965287411712962501496369098122086616168418882715222436234216425888991997985012509038279256180724250317055987984781404851415996782453786196006350659773832904598016699319318513372602854062680843911605280540706471936:ℝ)+(-1015/1629)*α+(20/1629)*α^2=row10PCoeffs α 1-(-4716185376616170246486000281589164524053479274631976465444377828265843090047804112270116337861298137217508108733000857569772707871619563621454120760649407726297392763421498647144361346477932582763691620748992033122647665106779519390059/2529051972357854855357687586705416662513467321883098779545515769944437001926107947833000927981865112581344513305626518252853503891863032643662743971042084075764057155937964496141382150293873866620353425686564127595204447524866358247424) := by
    dsimp [row10PCoeffs]
    ring
  rw [he1] at h1
  norm_num at h1
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have h2 := quadratic_midpoint_bound α (194321947296730718601147848629408529324060800528524268971722372112766700316491983402861459659286240459025588037238647/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (-87392508157403339069793311737287696734404939865622134266310618077493888260939941529767421027432567245256371917363866848437825591479028483329337639982887312677287844488188920717494066958850007246878328408693770720792211943538945354135555/610344542662362305092988604258240554553250113681121172130317805813257463131500718077030890619623447169631142544424533071688645605902945211337275545011489623617725793633028765068786892270921559811045293399024142792976006669334414457044992) (617795/9730017) (-21415/9730017) hm
  have he2 : (-87392508157403339069793311737287696734404939865622134266310618077493888260939941529767421027432567245256371917363866848437825591479028483329337639982887312677287844488188920717494066958850007246878328408693770720792211943538945354135555/610344542662362305092988604258240554553250113681121172130317805813257463131500718077030890619623447169631142544424533071688645605902945211337275545011489623617725793633028765068786892270921559811045293399024142792976006669334414457044992:ℝ)+(617795/9730017)*α+(-21415/9730017)*α^2=row10PCoeffs α 2-(505865247654323288914036995752361133665194090844208561641855457159019451019910887503237928742032737630462274325386051959582319739776091974649957617689491005387930820918698998832258543762598435169504260158005485833405996851923933615896603/5493100883961260745836897438324164990979251023130090549172860252319317168183506462693278015576611024526680282899820797645197810453126506902035479905103406612559532142697258885619082030438294038299407640591217285136784060024009730113404928) := by
    dsimp [row10PCoeffs]
    ring
  rw [he2] at h2
  norm_num at h2
  have h2lo := (abs_le.mp h2).1
  have h2hi := (abs_le.mp h2).2
  refine ⟨by linarith only [hlo],by linarith only [hhi],by linarith only [h1lo,h1hi],
    by linarith only [h1lo,h1hi],by linarith only [h2lo,h2hi],by linarith only [h2lo,h2hi],?_⟩
  calc
    _ ≤ ∑ i : Fin 29, row10PBounds2 ⟨i.val+3,by omega⟩ * ((2*i.val+3:ℕ):ℝ)*(5/4:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact row10_p_coefficient_bounds_2 α hlo hhi _
    _ ≤ _ := by norm_num [row10PBounds2,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row10Estimates3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_branch_estimates_3 (α : ℝ)
    (hlo : (342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    (43413/2500:ℝ) < α ∧ α < (173653/10000:ℝ) ∧
    (37603/5000:ℝ) < -row10PCoeffs α 1 ∧ -row10PCoeffs α 1 < (75207/10000:ℝ) ∧
    (387/1000:ℝ) < row10PCoeffs α 2 ∧ row10PCoeffs α 2 < (97/250:ℝ) ∧
    (∑ i : Fin 29, |row10PCoeffs α ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*(5/4:ℝ)^(i.val+1)) ≤ (1/20:ℝ)-1/10000 := by
  have hm : |α-(1368454411899111887120711722121899420795960997849082462032048820866607474609986219561800811974020489811926885335168181/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by rw [abs_le]; constructor <;> linarith only [hlo,hhi]
  have h1 := quadratic_midpoint_bound α (1368454411899111887120711722121899420795960997849082462032048820866607474609986219561800811974020489811926885335168181/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (6000328696821285048026151827244008627759665496636589401912432501416240275578479330308464634340064896858554545653455216260605946152970909011911438268588437181720683255536735745522536799213469828911226837632975036589070675287512055422305/843017324119284951785895862235138887504489107294366259848505256648145667308702649277666975993955037527114837768542172750951167963954344214554247990347361358588019051979321498713794050097957955540117808562188042531734815841622119415808) (-1015/1629) (20/1629) hm
  have he1 : (6000328696821285048026151827244008627759665496636589401912432501416240275578479330308464634340064896858554545653455216260605946152970909011911438268588437181720683255536735745522536799213469828911226837632975036589070675287512055422305/843017324119284951785895862235138887504489107294366259848505256648145667308702649277666975993955037527114837768542172750951167963954344214554247990347361358588019051979321498713794050097957955540117808562188042531734815841622119415808:ℝ)+(-1015/1629)*α+(20/1629)*α^2=row10PCoeffs α 1-(-19020214218059270560003760515907658810805142160146879530950085167212823277174044416801615578416201103350158832163032198341669480757874102683717489401829846963049774458367895199561359557657553865761465671869599971502173179822066408249379/2529051972357854855357687586705416662513467321883098779545515769944437001926107947833000927981865112581344513305626518252853503891863032643662743971042084075764057155937964496141382150293873866620353425686564127595204447524866358247424) := by
    dsimp [row10PCoeffs]
    ring
  rw [he1] at h1
  norm_num at h1
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have h2 := quadratic_midpoint_bound α (1368454411899111887120711722121899420795960997849082462032048820866607474609986219561800811974020489811926885335168181/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (-8839884154895719925083012953640479690934677098686836258252337856732448244817194465322646295502345537953978513806345696871563460655373998644839852874671995902684244241993136518852185422637450020931160238144369931432451645915775409858381275/20141369907857956068068623940521938300257253751476998680300487591837496283339523696542019390447573756597827703966009591365725304994797191974130092985379157579384951189889949247269967444940411473764494682167796712168208220088035677082484736) (617795/9730017) (-21415/9730017) hm
  have he2 : (-8839884154895719925083012953640479690934677098686836258252337856732448244817194465322646295502345537953978513806345696871563460655373998644839852874671995902684244241993136518852185422637450020931160238144369931432451645915775409858381275/20141369907857956068068623940521938300257253751476998680300487591837496283339523696542019390447573756597827703966009591365725304994797191974130092985379157579384951189889949247269967444940411473764494682167796712168208220088035677082484736:ℝ)+(617795/9730017)*α+(-21415/9730017)*α^2=row10PCoeffs α 2-(23432311881301785385393907952205929566415077248650211660452672409274663757837548947056581420953572570516639739179260844174751165547235187806064666060294544812268475151754395392679487620374782132217073063710486837106391920708133909290586513/60424109723573868204205871821565814900771761254430996040901462775512488850018571089626058171342721269793483111898028774097175914984391575922390278956137472738154853569669847741809902334821234421293484046503390136504624660264107031247454208) := by
    dsimp [row10PCoeffs]
    ring
  rw [he2] at h2
  norm_num at h2
  have h2lo := (abs_le.mp h2).1
  have h2hi := (abs_le.mp h2).2
  refine ⟨by linarith only [hlo],by linarith only [hhi],by linarith only [h1lo,h1hi],
    by linarith only [h1lo,h1hi],by linarith only [h2lo,h2hi],by linarith only [h2lo,h2hi],?_⟩
  calc
    _ ≤ ∑ i : Fin 29, row10PBounds3 ⟨i.val+3,by omega⟩ * ((2*i.val+3:ℕ):ℝ)*(5/4:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact row10_p_coefficient_bounds_3 α hlo hhi _
    _ ≤ _ := by norm_num [row10PBounds3,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: NewtonError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators





theorem newton_polynomial_error_hasDerivAt (c : Fin 32 → ℝ) (w : ℂ) :
    HasDerivAt (newtonPolynomialError c)
      (∑ i : Fin 29, (c ⟨i.val+3,by omega⟩:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)) w := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (c ⟨i.val+3,by omega⟩:ℂ)

theorem newton_polynomial_error_deriv_bound (c : Fin 32 → ℝ) (R : ℝ)
    (w : ℂ) (hw : ‖w‖^2 ≤ R) :
    ‖deriv (newtonPolynomialError c) w‖ ≤
      ∑ i : Fin 29, |c ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*R^(i.val+1) := by
  rw [(newton_polynomial_error_hasDerivAt c w).deriv]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
  rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
  gcongr

theorem newton_error_differentiableAt (c : Fin 32 → ℝ) (Y : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ Y (Metric.ball 0 2)) (w : ℂ) (hw : ‖w‖^2 ≤ 10/7) :
    DifferentiableAt ℂ (newtonError c Y) w := by
  exact (newton_polynomial_error_hasDerivAt c w).differentiableAt.add
    (newton_tail_differentiableAt Y hhol w (by nlinarith [norm_nonneg w]))

theorem newton_error_deriv_bound (c : Fin 32 → ℝ) (Y : ℂ → ℂ) (R δ : ℝ)
    (hR : R ≤ 10/7) (hhol : DifferentiableOn ℂ Y (Metric.ball 0 2))
    (hY : ∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000)
    (hcoeff : (∑ i : Fin 29, |c ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*R^(i.val+1)) ≤ δ-1/10000)
    (w : ℂ) (hw : ‖w‖^2 ≤ R) : ‖deriv (newtonError c Y) w‖ ≤ δ := by
  have hp := newton_polynomial_error_deriv_bound c R w hw
  have ht := newton_tail_deriv_bound Y hhol hY w (hw.trans hR)
  have hn : ‖w‖ ≤ 7/5 := by nlinarith [norm_nonneg w]
  have hd : deriv (newtonError c Y) w = deriv (newtonPolynomialError c) w+deriv (newtonTail Y) w := by
    exact deriv_add (newton_polynomial_error_hasDerivAt c w).differentiableAt (newton_tail_differentiableAt Y hhol w hn)
  rw [hd]
  have hs := norm_add_le (deriv (newtonPolynomialError c) w) (deriv (newtonTail Y) w)
  linarith only [hp,ht,hcoeff,hs]

theorem newton_error_axes (c : Fin 32 → ℝ) (Y : ℂ → ℂ)
    (hY : ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0) (x : ℝ) (hx : x^2 ≤ 10/7) :
    (newtonError c Y (x:ℂ)).im=0 ∧ (newtonError c Y (Complex.I*(x:ℂ))).re=0 := by
  obtain ⟨hr,hi⟩ := newton_tail_axes Y hY x hx
  constructor
  · rw [newtonError,Complex.add_im,hr,add_zero]
    norm_num [newtonPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [newtonError,Complex.add_re,hi,add_zero]
    norm_num [newtonPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
      ← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re] <;> norm_num [Complex.I_pow_three]

theorem newton_error_coordinate_bounds (c : Fin 32 → ℝ) (Y : ℂ → ℂ) (R δ : ℝ)
    (hR : R ≤ 10/7) (hhol : DifferentiableOn ℂ Y (Metric.ball 0 2))
    (hY : ∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000)
    (hreal : ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0)
    (hcoeff : (∑ i : Fin 29, |c ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*R^(i.val+1)) ≤ δ-1/10000)
    (w : ℂ) (hw : ‖w‖^2 ≤ R) :
    |(newtonError c Y w).re| ≤ δ*|w.re| ∧ |(newtonError c Y w).im| ≤ δ*|w.im| :=
  analytic_error_coordinate_bounds (newtonError c Y) R δ
    (fun v hv => newton_error_differentiableAt c Y hhol v (hv.trans hR))
    (newton_error_deriv_bound c Y R δ hR hhol hY hcoeff)
    (fun x hx => newton_error_axes c Y hreal x (hx.trans hR)) w hw

theorem newton_remainder_identity (c : Fin 32 → ℝ) (Y : ℂ → ℂ) (w : ℂ) :
    w^3*((c 2:ℂ)*w+newtonError c Y w) =
      (∑ i : Fin 32, (c i:ℂ)*(w^2)^i.val)+(w^2)^32*Y (w^2)-(c 0:ℂ)-(c 1:ℂ)*w^2 := by
  norm_num [newtonError,newtonPolynomialError,newtonTail,Fin.sum_univ_succ,Fin.succ]
  ring <;> rfl

theorem newton_inverse_exact (c : Fin 32 → ℝ) (Y : ℂ → ℂ) (β z : ℂ) (hz : z ≠ 0)
    (hbranch : β/z^3 = (∑ i : Fin 32, (c i:ℂ)*((z⁻¹)^2)^i.val)+((z⁻¹)^2)^32*Y ((z⁻¹)^2)) :
    β/z=(c 0:ℂ)*z^2+(c 1:ℂ)+newtonRemainder c Y z/z := by
  have hh := newton_remainder_identity c Y z⁻¹
  change (z⁻¹)^3*newtonRemainder c Y z = _ at hh
  rw [← hbranch] at hh
  apply mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero hz))
  calc
    _ = β/z^3 := by field_simp <;> ring
    _ = _ := by
      rw [show β/z^3 = (z⁻¹)^3*newtonRemainder c Y z+(c 0:ℂ)+(c 1:ℂ)*(z⁻¹)^2 by linear_combination -hh]
      field_simp <;> ring
end DerivativeChainPrivate

end


section
-- Source module: NewtonReal

set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem real_newton_branch_value (c : Fin 32 → ℝ) (Y : ℂ → ℂ) (t : ℝ)
    (hY : (Y (t:ℂ)).im=0) :
    ((∑ i : Fin 32, (c i:ℂ)*(t:ℂ)^i.val)+(t:ℂ)^32*Y (t:ℂ)).im=0 := by
  have hr : Y (t:ℂ)=((Y (t:ℂ)).re:ℂ) := by apply Complex.ext <;> simp [hY]
  rw [hr]
  simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_sum,
    ← Complex.ofReal_add,Complex.ofReal_im]
end DerivativeChainPrivate

end


section
-- Source module: FifthDecicUpperData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
theorem fifth_decic_upper_data (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 4/5 ≤ z.re^2)
    (hroot : (fifthUnitP10 β).eval z=0) :
    ∃ α b : ℝ, ∃ e : ℂ, 1 < α ∧ β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((1461/1250 < α ∧ α < 11689/10000 ∧ 2229/2000 < b ∧ b < 5573/5000 ∧
          0 < e.re/z.re ∧ e.re/z.re ≤ (23/1000)/(z.re^2+z.im^2) ∧
          -(23/1000)/(z.re^2+z.im^2) ≤ e.im/z.im ∧ e.im/z.im < 0) ∨ (12329/5000 < α ∧ b < 18649/10000 ∧ 0 ≤ e.re/z.re ∧ e.re/z.re ≤ 17/100 ∧
          -(17/100) ≤ e.im/z.im ∧ e.im/z.im ≤ 0) ∨ (17 < α ∧ b < 7521/1000 ∧ 0 ≤ e.re/z.re ∧ e.re/z.re ≤ 11/20 ∧ -(11/20) ≤ e.im/z.im ∧ e.im/z.im ≤ 0)) := by
  obtain ⟨a1,a2,a3,Y1,Y2,Y3,⟨hl1,hu1⟩,⟨hl2,hu2⟩,⟨hl3,hu3⟩,
    ⟨hol1,norm1,real1⟩,⟨hol2,norm2,real2⟩,⟨hol3,norm3,real3⟩,hcover⟩ := row10_complete_inverse_branches
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hn : ‖z⁻¹‖^2 ≤ 5/4 := by
    convert inverse_norm_square_bound z (4/5) (by norm_num) hX using 1 <;> norm_num
  have ht : ‖(z⁻¹)^2‖ ≤ 5/4 := by simpa only [norm_pow] using hn
  have heq := fifth_decic_inverse_equation β z hz hroot
  have hc := hcover ((z⁻¹)^2) ht (β/z^3) (by simpa only [sub_eq_add_neg,neg_mul] using heq)
  let U := z.re^2+z.im^2
  have hU : 4/5 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith only [hU]
  rcases hc with hbranch|hbranch|hbranch
  · let e := newtonRemainder (row10PCoeffs a1) Y1 z
    let b := -row10PCoeffs a1 1
    let γ := row10PCoeffs a1 2
    obtain ⟨hal,hau,hbl,hbu,hgl,hgu,hcoeff⟩ := row10_branch_estimates_1 a1 hl1 hu1
    change _ < b at hbl
    change b < _ at hbu
    change _ < γ at hgl
    change γ < _ at hgu
    have hg := newton_inverse_exact (row10PCoeffs a1) Y1 β z hz hbranch
    have ha0 : row10PCoeffs a1 0=a1 := by norm_num [row10PCoeffs]
    rw [ha0] at hg
    have hgraph : β/z=(a1:ℂ)*z^2-(b:ℂ)+e/z := by simpa only [b,Complex.ofReal_neg,sub_neg_eq_add] using hg
    have herr := newton_error_coordinate_bounds (row10PCoeffs a1) Y1 (5/4) (1/500)
      (by norm_num) hol1 norm1 real1 hcoeff z⁻¹ hn
    obtain ⟨hAl,hAu,hBl,hBu⟩ := inverse_error_coordinate_bounds (newtonError (row10PCoeffs a1) Y1) γ (1/500) z hx hy herr
    change (γ-(1/500))/U ≤ e.re/z.re at hAl
    change e.re/z.re ≤ (γ+(1/500))/U at hAu
    change -(γ+(1/500))/U ≤ e.im/z.im at hBl
    change e.im/z.im ≤ -(γ-(1/500))/U at hBu
    have hlower : -(3/100) ≤ (γ-(1/500))/U := by
      apply (le_div_iff₀ hUp).mpr
      nlinarith only [hU,hgl]
    have hupper : (γ+(1/500))/U ≤ 3/100 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hU,hgu]
    have hAb : e.re/z.re ≤ 3/100 := hAu.trans hupper
    have hBb : -(3/100) ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hBl,hupper]
    have hphase : 0 < (β/z).im := cubic_graph_positive_phase_general β z e a1 b (3/100) (4/5)
      hx hy hX (by norm_num) (by linarith only [hal]) (by linarith only [hal]) hAb hBb hgraph
    have hpos : 0 < (γ-(1/500))/U := div_pos (by linarith only [hgl]) hUp
    have hAp : 0 < e.re/z.re := hpos.trans_le hAl
    have hBn : e.im/z.im < 0 := by
      simp only [neg_div] at hBu
      linarith only [hpos,hBu]
    have hrecip : (γ+(1/500))/U ≤ (23/1000)/U := div_le_div_of_nonneg_right (by linarith only [hgu]) hUp.le
    have hBlo : -(23/1000)/U ≤ e.im/z.im := by
      simp only [neg_div] at hBl ⊢
      linarith only [hBl,hrecip]
    exact ⟨a1,b,e,by linarith only [hal],hgraph,hphase,Or.inl ⟨hal,hau,hbl,hbu,hAp,hAu.trans hrecip,hBlo,hBn⟩⟩
  · let e := newtonRemainder (row10PCoeffs a2) Y2 z
    let b := -row10PCoeffs a2 1
    let γ := row10PCoeffs a2 2
    obtain ⟨hal,hau,hbl,hbu,hgl,hgu,hcoeff⟩ := row10_branch_estimates_2 a2 hl2 hu2
    change _ < b at hbl
    change b < _ at hbu
    change _ < γ at hgl
    change γ < _ at hgu
    have hg := newton_inverse_exact (row10PCoeffs a2) Y2 β z hz hbranch
    have ha0 : row10PCoeffs a2 0=a2 := by norm_num [row10PCoeffs]
    rw [ha0] at hg
    have hgraph : β/z=(a2:ℂ)*z^2-(b:ℂ)+e/z := by simpa only [b,Complex.ofReal_neg,sub_neg_eq_add] using hg
    have herr := newton_error_coordinate_bounds (row10PCoeffs a2) Y2 (5/4) (41/1000)
      (by norm_num) hol2 norm2 real2 hcoeff z⁻¹ hn
    obtain ⟨hAl,hAu,hBl,hBu⟩ := inverse_error_coordinate_bounds (newtonError (row10PCoeffs a2) Y2) γ (41/1000) z hx hy herr
    change (γ-(41/1000))/U ≤ e.re/z.re at hAl
    change e.re/z.re ≤ (γ+(41/1000))/U at hAu
    change -(γ+(41/1000))/U ≤ e.im/z.im at hBl
    change e.im/z.im ≤ -(γ-(41/1000))/U at hBu
    have hlower : -(17/100) ≤ (γ-(41/1000))/U := by
      apply (le_div_iff₀ hUp).mpr
      nlinarith only [hU,hgl]
    have hupper : (γ+(41/1000))/U ≤ 17/100 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hU,hgu]
    have hAb : e.re/z.re ≤ 17/100 := hAu.trans hupper
    have hBb : -(17/100) ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hBl,hupper]
    have hphase : 0 < (β/z).im := cubic_graph_positive_phase_general β z e a2 b (17/100) (4/5)
      hx hy hX (by norm_num) (by linarith only [hal]) (by linarith only [hal]) hAb hBb hgraph
    have hpos : 0 < (γ-(41/1000))/U := div_pos (by linarith only [hgl]) hUp
    have hAp : 0 < e.re/z.re := hpos.trans_le hAl
    have hBn : e.im/z.im < 0 := by
      simp only [neg_div] at hBu
      linarith only [hpos,hBu]
    exact ⟨a2,b,e,by linarith only [hal],hgraph,hphase,Or.inr (Or.inl ⟨by linarith only [hal],by linarith only [hbu],hAp.le,hAb,hBb,hBn.le⟩)⟩
  · let e := newtonRemainder (row10PCoeffs a3) Y3 z
    let b := -row10PCoeffs a3 1
    let γ := row10PCoeffs a3 2
    obtain ⟨hal,hau,hbl,hbu,hgl,hgu,hcoeff⟩ := row10_branch_estimates_3 a3 hl3 hu3
    change _ < b at hbl
    change b < _ at hbu
    change _ < γ at hgl
    change γ < _ at hgu
    have hg := newton_inverse_exact (row10PCoeffs a3) Y3 β z hz hbranch
    have ha0 : row10PCoeffs a3 0=a3 := by norm_num [row10PCoeffs]
    rw [ha0] at hg
    have hgraph : β/z=(a3:ℂ)*z^2-(b:ℂ)+e/z := by simpa only [b,Complex.ofReal_neg,sub_neg_eq_add] using hg
    have herr := newton_error_coordinate_bounds (row10PCoeffs a3) Y3 (5/4) (1/20)
      (by norm_num) hol3 norm3 real3 hcoeff z⁻¹ hn
    obtain ⟨hAl,hAu,hBl,hBu⟩ := inverse_error_coordinate_bounds (newtonError (row10PCoeffs a3) Y3) γ (1/20) z hx hy herr
    change (γ-(1/20))/U ≤ e.re/z.re at hAl
    change e.re/z.re ≤ (γ+(1/20))/U at hAu
    change -(γ+(1/20))/U ≤ e.im/z.im at hBl
    change e.im/z.im ≤ -(γ-(1/20))/U at hBu
    have hlower : -(11/20) ≤ (γ-(1/20))/U := by
      apply (le_div_iff₀ hUp).mpr
      nlinarith only [hU,hgl]
    have hupper : (γ+(1/20))/U ≤ 11/20 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hU,hgu]
    have hAb : e.re/z.re ≤ 11/20 := hAu.trans hupper
    have hBb : -(11/20) ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hBl,hupper]
    have hphase : 0 < (β/z).im := cubic_graph_positive_phase_general β z e a3 b (11/20) (4/5)
      hx hy hX (by norm_num) (by linarith only [hal]) (by linarith only [hal]) hAb hBb hgraph
    have hpos : 0 < (γ-(1/20))/U := div_pos (by linarith only [hgl]) hUp
    have hAp : 0 < e.re/z.re := hpos.trans_le hAl
    have hBn : e.im/z.im < 0 := by
      simp only [neg_div] at hBu
      linarith only [hpos,hBu]
    exact ⟨a3,b,e,by linarith only [hal],hgraph,hphase,Or.inr (Or.inr ⟨by linarith only [hal],by linarith only [hbu],hAp.le,hAb,hBb,hBn.le⟩)⟩
end DerivativeChainPrivate

end


section
-- Source module: FifthDecicPhase

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_decic_real_root_parameter (β : ℂ) (x : ℝ) (hx : 0 < x) (hX : 4/5 ≤ x^2)
    (hroot : (fifthUnitP10 β).eval (x:ℂ)=0) : β.im=0 := by
  obtain ⟨a1,a2,a3,Y1,Y2,Y3,_,_,_,⟨_,_,real1⟩,⟨_,_,real2⟩,⟨_,_,real3⟩,hcover⟩ := row10_complete_inverse_branches
  have hz : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hn : ‖(x:ℂ)⁻¹‖^2 ≤ 5/4 := by
    convert inverse_norm_square_bound (x:ℂ) (4/5) (by norm_num) (by simpa using hX) using 1 <;> norm_num
  have ht : ((x:ℂ)⁻¹)^2=(((x⁻¹)^2:ℝ):ℂ) := by norm_cast
  have hs : |(x⁻¹)^2| ≤ 5/4 := by
    have hh : ‖((x:ℂ)⁻¹)^2‖ ≤ 5/4 := by simpa only [norm_pow] using hn
    rw [ht] at hh
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hh
  have htc : ‖(((x⁻¹)^2:ℝ):ℂ)‖ ≤ 5/4 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hs
  have hs2 : |(x⁻¹)^2| ≤ 2 := by linarith only [hs]
  have heq := fifth_decic_inverse_equation β (x:ℂ) hz hroot
  rw [ht] at heq
  have hc := hcover (((x⁻¹)^2:ℝ):ℂ) htc (β/(x:ℂ)^3) (by simpa only [sub_eq_add_neg,neg_mul] using heq)
  have him : (β/(x:ℂ)^3).im=0 := by
    rcases hc with h|h|h
    · rw [h]
      exact real_newton_branch_value (row10PCoeffs a1) Y1 _ (real1 _ hs2)
    · rw [h]
      exact real_newton_branch_value (row10PCoeffs a2) Y2 _ (real2 _ hs2)
    · rw [h]
      exact real_newton_branch_value (row10PCoeffs a3) Y3 _ (real3 _ hs2)
  simpa [Complex.div_im,← Complex.ofReal_pow,hx.ne'] using him

theorem fifth_decic_nonnegative_im (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 4/5 ≤ z.re^2) (hroot : (fifthUnitP10 β).eval z=0) :
    0 ≤ z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0 ≤ z.im := by
    by_contra hn
    have hy : z.im < 0 := lt_of_not_ge hn
    have hroot' : (fifthUnitP10 (starRingEnd ℂ β)).eval (starRingEnd ℂ z)=0 := by
      simpa [fifthUnitP10,map_ofNat] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_decic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
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
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_decic_upper_data β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    exact fifth_decic_real_root_parameter β z.re hx hX hroot
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w E₀ : ℂ) (α₀ b₀ : ℝ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 4/5 ≤ w.re^2)
    (hwroot : (fifthUnitP9 β).eval w=0)
    (hα₀lo : 7343/5000 < α₀) (hα₀up : α₀ < 14687/10000)
    (hb₀lo : 12919/10000 < b₀) (hb₀up : b₀ < 323/250)
    (hwinv : β/w=(α₀:ℂ)*w^2-(b₀:ℂ)+E₀/w)
    (hA₀ : E₀.re/w.re ≤ 1/16) (hB₀ : E₀.im/w.im ≤ 0)
    (hC₀ : (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 1/8)
    (hW₀ : 4/5 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ, ∃ α b : ℝ, ∃ e : ℂ,
      (fifthUnitP10 β).eval z=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧
      1461/1250 < α ∧ α < 11689/10000 ∧ 2229/2000 < b ∧ b < 5573/5000 ∧
      β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ e.re/z.re ≤ 3/100 ∧ e.im/z.im ≤ 0 ∧
      (3*(e.re/z.re)-e.im/z.im)/2 ≤ 3/50 := by
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  obtain ⟨hr₀,hi₀,_⟩ := cubic_graph_coordinate_parts β w E₀ α₀ b₀ hw hwinv
  have hR₀ : β.re/w.re=α₀*(w.re^2-3*w.im^2)-b₀+E₀.re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im=α₀*(3*w.re^2-w.im^2)-b₀+E₀.im/w.im := by rw [hi₀]; field_simp
  have hcritical : (fifthUnitP10 β).derivative.eval w=0 := by rw [fifth_decic_derivative,hwroot,mul_zero]
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent (fifthUnitP10 β) (by rw [fifth_unit_p10_degree]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 4/5 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  obtain ⟨hy0,hzero⟩ := fifth_decic_nonnegative_im β z hR hI.le hx hX hz
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith only [this,hI]
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fifth_decic_upper_data β z hx hy hX hz
  obtain ⟨hr₁,hi₁,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re=α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im=α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  rcases hcases with hs|hmid|hhigh
  · obtain ⟨hal,hau,hbl,hbu,hAp,hAr,hBr,hBn⟩ := hs
    have hC₁ : 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2 := by linarith only [hAp,hBn]
    have himorder : w.im ≤ z.im := by
      by_contra hn
      exact inverse_graph_southeast_impossible α₀ α b₀ b (E₀.re/w.re) (e.re/z.re)
        (E₀.im/w.im) (e.im/z.im) (1/8) β.re β.im w.re w.im z.re z.im
        (by linarith only [hal]) (by linarith only [hau,hα₀lo]) hwpos hy hxz (le_of_not_ge hn)
        hR hI.le hC₀ hC₁ (by linarith only [hb₀lo,hbu]) hR₀ hI₀ hR₁ hI₁
    have hU : 4/5 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
    have hUp : 0 < z.re^2+z.im^2 := by linarith only [hU]
    have hc : (23/1000:ℝ)/(z.re^2+z.im^2) ≤ 3/100 := by
      apply (div_le_iff₀ hUp).mpr
      linarith only [hU]
    refine ⟨z,α,b,e,hz,hxz,himorder,hal,hau,hbl,hbu,hgraph,hAr.trans hc,hBn.le,?_⟩
    simp only [neg_div] at hBr
    linarith only [hAr,hBr,hc]
  · exfalso
    obtain ⟨hfast,hb,hAlo,hAhi,hBlo,hBhi⟩ := hmid
    by_cases hvy : z.im ≤ w.im
    · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ α b₀ b
        (E₀.re/w.re) (e.re/z.re) (4/5) (1/16) 0 hR hwpos hy.le hxz hvy hW₀
        (by linarith only [hfast]) (by linarith only [hfast,hα₀up]) hA₀ hAlo
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hR₀ hR₁
    · exact fast_graph_northeast_impossible α₀ α b₀ b (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
        (4/5) (23/100) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
        hR hI.le hwX (by linarith only [hα₀lo]) (by linarith only [hfast])
        (by linarith only [hfast,hα₀up]) hB₀ (by linarith only [hBlo,hAhi])
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hI₀ hR₁ hI₁
  · exfalso
    obtain ⟨hfast,hb,hAlo,hAhi,hBlo,hBhi⟩ := hhigh
    by_cases hvy : z.im ≤ w.im
    · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ α b₀ b
        (E₀.re/w.re) (e.re/z.re) (4/5) (1/16) 0 hR hwpos hy.le hxz hvy hW₀
        (by linarith only [hfast]) (by linarith only [hfast,hα₀up]) hA₀ hAlo
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hR₀ hR₁
    · exact fast_graph_northeast_impossible α₀ α b₀ b (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
        (4/5) (3/4) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
        hR hI.le hwX (by linarith only [hα₀lo]) (by linarith only [hfast])
        (by linarith only [hfast,hα₀up]) hB₀ (by linarith only [hBlo,hAhi])
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hI₀ hR₁ hI₁
