-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_nonic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T22:00:50.517899+00:00
-- url     : https://prove2.me/submissions/942cdfcc-811c-45b9-8e67-f617db484244

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Definitions.Def_DerivativeChainPrivate_fifth_row9_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row9_complete_inverse_branches
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
-- Source module: FifthOcticAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators














theorem fifth_octic_poly_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) : ‖fifthOcticPoly u-1‖ ≤ 1/2 := by
  have hs := norm_real_power_sum_le fifthOcticCoeffs u (9/4) (by norm_num) hu
  calc
    _ = ‖u‖*‖∑ i : Fin 16, (fifthOcticCoeffs i:ℂ)*u^i.val‖ := by simp [fifthOcticPoly,norm_mul]
    _ ≤ (9/4)*(∑ i : Fin 16, |fifthOcticCoeffs i| *(9/4:ℝ)^i.val) := mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _ ≤ 1/2 := by norm_num [fifthOcticCoeffs,Fin.sum_univ_succ]

theorem fifth_octic_residual_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) : ‖fifthOcticResidual u‖ ≤ 1/10000000000000 := by
  apply (norm_real_power_sum_le fifthOcticResidualCoeffs u (9/4) (by norm_num) hu).trans
  norm_num [fifthOcticResidualCoeffs,Fin.sum_univ_succ]
theorem fifth_octic_coefficient_bounds :
    (57/1000:ℝ) < fifthOcticExpansionCoeffs 0 ∧ fifthOcticExpansionCoeffs 0 < 3/50 ∧
    |fifthOcticRationalTailCoeff| ≤ 651/500000000000000000 ∧
    ∀ i : Fin 14, |fifthOcticErrorCoeffs i| ≤ fifthOcticErrorCoeffBounds i := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
  have hp := Real.sqrt_nonneg 22
  have hl : (4690415759/1000000000:ℝ) ≤ Real.sqrt 22 := by nlinarith only [hs,hp]
  have hu : Real.sqrt 22 ≤ (58630197/12500000:ℝ) := by nlinarith only [hs,hp]
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [fifthOcticExpansionCoeffs]; linarith only [hl,hu]
  · norm_num [fifthOcticExpansionCoeffs]; linarith only [hl,hu]
  · rw [abs_le]; dsimp [fifthOcticRationalTailCoeff]; constructor <;> linarith only [hl,hu]
  · intro i
    fin_cases i <;> norm_num [fifthOcticErrorCoeffs,fifthOcticErrorCoeffBounds,abs_le] <;> constructor <;> linarith only [hl,hu]
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
-- Source module: FifthOcticSlit

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_radicand_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    ‖fifthOcticRadicand u-1‖ ≤ 3/4 := by
  have he : fifthOcticRadicand u-1 = -(1/4:ℂ)*u+(1/66:ℂ)*u^2+(1/1188:ℂ)*u^3 := by
    dsimp [fifthOcticRadicand]; ring
  rw [he]
  calc
    _ ≤ ‖-(1/4:ℂ)*u‖+‖(1/66:ℂ)*u^2‖+‖(1/1188:ℂ)*u^3‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1/4:ℝ)*‖u‖+(1/66:ℝ)*‖u‖^2+(1/1188:ℝ)*‖u‖^3 := by norm_num [norm_mul,norm_pow]
    _ ≤ (1/4:ℝ)*(9/4)+(1/66:ℝ)*(9/4)^2+(1/1188:ℝ)*(9/4)^3 := by gcongr
    _ ≤ 3/4 := by norm_num

theorem fifth_octic_slit (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    fifthOcticRadicand u ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hn := fifth_octic_radicand_bound u hu
  have hr := Complex.re_le_norm (1-fifthOcticRadicand u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  linarith

theorem fifth_octic_denominator_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u ≠ 0 ∧
      ‖(Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u)⁻¹‖ ≤ 2 := by
  have hs : 0 ≤ (Complex.sqrt (fifthOcticRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp := fifth_octic_poly_bound u hu
  have hr := Complex.re_le_norm (1-fifthOcticPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd := Complex.re_le_norm (Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/2:ℝ) ≤ ‖Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

theorem fifth_octic_pole_bound (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    1-(1/12:ℂ)*u ≠ 0 ∧ ‖(1-(1/12:ℂ)*u)⁻¹‖ ≤ 2 := by
  have hn := norm_sub_norm_le (1:ℂ) ((1/12:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (1/2:ℝ) ≤ ‖1-(1/12:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hl
  norm_num at hi
  exact hi

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticTail


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_octic_tail_norm (w : ℂ) (hw : ‖w‖ ≤ 3/2) : ‖fifthOcticTail w‖ ≤ 1/1000000 := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hk : 0 < (3*Real.sqrt 22/4:ℝ) := by positivity
  have hku : (3*Real.sqrt 22/4:ℝ) ≤ 18/5 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
    have hp := Real.sqrt_nonneg 22
    nlinarith
  have hf : ‖1-(1/3:ℂ)*w^2‖ ≤ 7/4 := by
    calc
      _ ≤ ‖(1:ℂ)‖+‖(1/3:ℂ)*w^2‖ := norm_sub_le _ _
      _ = 1+(1/3:ℝ)*‖w^2‖ := by norm_num [norm_mul]
      _ ≤ 7/4 := by linarith
  have ht := fifth_octic_residual_bound (w^2) hu
  have hd := (fifth_octic_denominator_bound (w^2) hu).2
  have hp := (fifth_octic_pole_bound (w^2) hu).2
  have hL : |fifthOcticRationalTailCoeff| ≤ 1/100000000000000 := by
    have hh := fifth_octic_coefficient_bounds.2.2.1
    linarith only [hh]
  have h1 : ‖(fifthOcticRationalTailCoeff:ℂ)*w^31/(1-(1/12:ℂ)*w^2)‖ ≤ (1/100000000000000:ℝ)*(3/2)^31*2 := by
    calc
      _ = |fifthOcticRationalTailCoeff| * ‖w‖^31*‖(1-(1/12:ℂ)*w^2)⁻¹‖ := by
        simp [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by gcongr
  have h2 : ‖((3*Real.sqrt 22/4:ℝ):ℂ)*w^31*(1-(1/3:ℂ)*w^2)*fifthOcticResidual (w^2)/
      (Complex.sqrt (fifthOcticRadicand (w^2))+fifthOcticPoly (w^2))/(1-(1/12:ℂ)*w^2)‖ ≤
      (18/5:ℝ)*(3/2)^31*(7/4)*(1/10000000000000)*2*2 := by
    calc
      _ = (3*Real.sqrt 22/4:ℝ)*‖w‖^31*‖1-(1/3:ℂ)*w^2‖*‖fifthOcticResidual (w^2)‖*
          ‖(Complex.sqrt (fifthOcticRadicand (w^2))+fifthOcticPoly (w^2))⁻¹‖*‖(1-(1/12:ℂ)*w^2)⁻¹‖ := by
        simp only [div_eq_mul_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
        norm_num [abs_of_nonneg (Real.sqrt_nonneg 22)]
      _ ≤ _ := by gcongr
  unfold fifthOcticTail
  apply (norm_sub_le _ _).trans
  have hh := add_le_add h1 h2
  apply hh.trans
  norm_num

theorem fifth_octic_tail_differentiableAt (w : ℂ) (hw : ‖w‖ ≤ 3/2) :
    DifferentiableAt ℂ fifthOcticTail w := by
  have hu : ‖w^2‖ ≤ 9/4 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => fifthOcticRadicand (v^2)) w := by
    unfold fifthOcticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (fifthOcticRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (fifth_octic_slit (w^2) hu)).comp w hh
  have hpoly : DifferentiableAt ℂ (fun v : ℂ => fifthOcticPoly (v^2)) w := by unfold fifthOcticPoly; fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => fifthOcticResidual (v^2)) w := by unfold fifthOcticResidual; fun_prop
  have hd := (fifth_octic_denominator_bound (w^2) hu).1
  have hp := (fifth_octic_pole_bound (w^2) hu).1
  unfold fifthOcticTail
  fun_prop

theorem fifth_octic_tail_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 2) :
    ‖deriv fifthOcticTail w‖ ≤ 1/25000 := by
  have hw' : ‖w‖ ≤ 29/20 := by nlinarith [norm_nonneg w]
  have hball : ∀ u ∈ Metric.ball w (1/20:ℝ), ‖u‖ ≤ 3/2 := by
    intro u hu
    have hd : ‖u-w‖ < 1/20 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    have hn := norm_le_norm_sub_add u w
    linarith
  have hd : DifferentiableOn ℂ fifthOcticTail (Metric.ball w (1/20:ℝ)) := by
    intro u hu
    exact (fifth_octic_tail_differentiableAt u (hball u hu)).differentiableWithinAt
  have hm : Set.MapsTo fifthOcticTail (Metric.ball w (1/20:ℝ))
      (Metric.closedBall (fifthOcticTail w) (1/500000:ℝ)) := by
    intro u hu
    rw [Metric.mem_closedBall,dist_eq_norm]
    have h1 := fifth_octic_tail_norm u (hball u hu)
    have h2 := fifth_octic_tail_norm w (by linarith)
    have hn := norm_sub_le (fifthOcticTail u) (fifthOcticTail w)
    linarith
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1/20)
  norm_num at hh
  exact hh

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators




theorem fifth_octic_polynomial_error_hasDerivAt (w : ℂ) :
    HasDerivAt fifthOcticPolynomialError
      (∑ i : Fin 14, (fifthOcticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)) w := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [show 2*i.val+3-1=2*i.val+2 by omega,mul_assoc] using
    (hasDerivAt_pow (2*i.val+3) w).const_mul (fifthOcticErrorCoeffs i:ℂ)

theorem fifth_octic_polynomial_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    ‖deriv fifthOcticPolynomialError w‖ ≤ 29/1000 := by
  rw [(fifth_octic_polynomial_error_hasDerivAt w).deriv]
  have hsum : ‖∑ i : Fin 14, (fifthOcticErrorCoeffs i:ℂ)*((2*i.val+3:ℕ):ℂ)*w^(2*i.val+2)‖ ≤
      ∑ i : Fin 14, fifthOcticErrorCoeffBounds i * ((2*i.val+3:ℕ):ℝ)*(5/3:ℝ)^(i.val+1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    rw [show 2*i.val+2=2*(i.val+1) by omega,pow_mul]
    have hb := fifth_octic_coefficient_bounds.2.2.2 i
    have hb0 : 0 ≤ fifthOcticErrorCoeffBounds i := (abs_nonneg _).trans hb
    gcongr
  apply hsum.trans
  norm_num [fifthOcticErrorCoeffBounds,Fin.sum_univ_succ]

theorem fifth_octic_error_differentiableAt (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    DifferentiableAt ℂ fifthOcticError w := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  exact (fifth_octic_polynomial_error_hasDerivAt w).differentiableAt.add (fifth_octic_tail_differentiableAt w hn)

theorem fifth_octic_error_deriv_bound (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    ‖deriv fifthOcticError w‖ ≤ 3/100 := by
  have hn : ‖w‖ ≤ 3/2 := by nlinarith [norm_nonneg w]
  have hp := fifth_octic_polynomial_error_deriv_bound w hw
  have ht := fifth_octic_tail_deriv_bound w (by linarith)
  have hd : deriv fifthOcticError w = deriv fifthOcticPolynomialError w+deriv fifthOcticTail w := by
    exact deriv_add (fifth_octic_polynomial_error_hasDerivAt w).differentiableAt (fifth_octic_tail_differentiableAt w hn)
  rw [hd]
  have hs := norm_add_le (deriv fifthOcticPolynomialError w) (deriv fifthOcticTail w)
  linarith

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticAxes


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem fifth_octic_radicand_real (x : ℝ) : fifthOcticRadicand (x:ℂ) = ((1-x/4+x^2/66+x^3/1188:ℝ):ℂ) := by
  simp [fifthOcticRadicand] <;> ring
theorem fifth_octic_poly_real (x : ℝ) : fifthOcticPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 16, fifthOcticCoeffs i*x^i.val):ℝ):ℂ) := by simp [fifthOcticPoly]
theorem fifth_octic_residual_real (x : ℝ) : fifthOcticResidual (x:ℂ) =
    ((∑ i : Fin 16, fifthOcticResidualCoeffs i*x^i.val : ℝ):ℂ) := by simp [fifthOcticResidual]
theorem fifth_octic_sqrt_real (x : ℝ) (hx : |x| ≤ 9/4) : Complex.sqrt (fifthOcticRadicand (x:ℂ)) =
    ((Real.sqrt (1-x/4+x^2/66+x^3/1188):ℝ):ℂ) := by
  have hp := fifth_octic_slit (x:ℂ) (by simpa using hx)
  have hreal := fifth_octic_radicand_real x
  have hpos : 0 < (fifthOcticRadicand (x:ℂ)).re := by
    have hb := fifth_octic_radicand_bound (x:ℂ) (by simpa using hx)
    have hr := Complex.re_le_norm (1-fifthOcticRadicand (x:ℂ))
    rw [norm_sub_rev] at hr
    simp only [Complex.sub_re,Complex.one_re] at hr
    linarith
  rw [hreal,Complex.ofReal_re] at hpos
  have hp : 0 ≤ 1-x/4+x^2/66+x^3/1188 := hpos.le
  rw [fifth_octic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp),Complex.ofReal_re]

theorem fifth_octic_tail_real_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthOcticTail (x:ℂ)).im = 0 := by
  unfold fifthOcticTail
  rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by norm_cast]
  rw [fifth_octic_sqrt_real _ (by rw [abs_of_nonneg (sq_nonneg x)]; linarith),fifth_octic_poly_real,fifth_octic_residual_real]
  rw [show (x:ℂ)^31=((x^31:ℝ):ℂ) by norm_cast]
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,show (1/12:ℂ)=((1/12:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,← Complex.ofReal_pow,Complex.ofReal_im]

theorem fifth_octic_tail_imaginary_axis (x : ℝ) (hx : x^2 ≤ 2) : (fifthOcticTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold fifthOcticTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [fifth_octic_sqrt_real _ (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith),fifth_octic_poly_real,fifth_octic_residual_real]
  have he : (Complex.I*(x:ℂ))^31 = -Complex.I*((x^31:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod] <;> norm_num [Complex.I_pow_three]
  rw [he]
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,show (1/12:ℂ)=((1/12:ℝ):ℂ) by norm_num]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div,← Complex.ofReal_pow]
  simp only [Complex.sub_re,Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,zero_sub,mul_one,one_mul,neg_zero,zero_div]

theorem fifth_octic_error_axes (x : ℝ) (hx : x^2 ≤ 2) :
    (fifthOcticError (x:ℂ)).im = 0 ∧ (fifthOcticError (Complex.I*(x:ℂ))).re = 0 := by
  constructor
  · rw [fifthOcticError,Complex.add_im,fifth_octic_tail_real_axis x hx,add_zero]
    norm_num [fifthOcticPolynomialError,Fin.sum_univ_succ,← Complex.ofReal_pow,Complex.mul_im,Complex.mul_re]
  · rw [fifthOcticError,Complex.add_re,fifth_octic_tail_imaginary_axis x hx,add_zero]
    norm_num [fifthOcticPolynomialError,Fin.sum_univ_succ,mul_pow,Complex.I_pow_eq_pow_mod,
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
-- Source module: FifthOcticCoordinates

set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_octic_leading_bounds : (57/1000:ℝ) < fifthOcticLeadingError ∧ fifthOcticLeadingError < 3/50 :=
  ⟨fifth_octic_coefficient_bounds.1,fifth_octic_coefficient_bounds.2.1⟩

theorem fifth_octic_error_coordinates (w : ℂ) (hw : ‖w‖^2 ≤ 5/3) :
    |(fifthOcticError w).re| ≤ (3/100)*|w.re| ∧ |(fifthOcticError w).im| ≤ (3/100)*|w.im| :=
  analytic_error_coordinate_bounds fifthOcticError (5/3) (3/100)
    fifth_octic_error_differentiableAt fifth_octic_error_deriv_bound
    (fun x hx => fifth_octic_error_axes x (by linarith)) w hw

theorem fifth_octic_remainder_bounds (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 3/5 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    0 < (fifthOcticRemainder z).re/z.re ∧ (fifthOcticRemainder z).re/z.re ≤ (9/100)/U ∧
      -(9/100)/U ≤ (fifthOcticRemainder z).im/z.im ∧ (fifthOcticRemainder z).im/z.im < 0 := by
  have hU : 3/5 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < z.re^2+z.im^2 := by linarith
  have hn : ‖z⁻¹‖^2 ≤ 5/3 := by
    rw [norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
    apply (inv_le_comm₀ (by nlinarith) (by norm_num)).mpr
    norm_num
    nlinarith
  obtain ⟨hAlo,hAhi,hBlo,hBhi⟩ := inverse_error_coordinate_bounds fifthOcticError fifthOcticLeadingError
    (3/100) z hx hy (fifth_octic_error_coordinates z⁻¹ hn)
  obtain ⟨hgl,hgu⟩ := fifth_octic_leading_bounds
  have hp : 0 < (fifthOcticLeadingError-3/100)/(z.re^2+z.im^2) := div_pos (by linarith) hUp
  have hu : (fifthOcticLeadingError+3/100)/(z.re^2+z.im^2) ≤ (9/100)/(z.re^2+z.im^2) :=
    div_le_div_of_nonneg_right (by linarith) hUp.le
  change 0 < _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ < _
  change (fifthOcticLeadingError-3/100)/_ ≤ (fifthOcticRemainder z).re/z.re at hAlo
  change (fifthOcticRemainder z).re/z.re ≤ _ at hAhi
  change _ ≤ (fifthOcticRemainder z).im/z.im at hBlo
  change (fifthOcticRemainder z).im/z.im ≤ _ at hBhi
  simp only [neg_div] at hBlo hBhi ⊢
  exact ⟨lt_of_lt_of_le hp hAlo,hAhi.trans hu,by linarith,by linarith⟩
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


 theorem fifth_unit_p9_degree (β : ℂ) : (fifthUnitP9 β).natDegree=9 := by
  unfold fifthUnitP9
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

theorem fifth_nonic_inverse_equation (β z : ℂ) (hz : z ≠ 0) (hroot : (fifthUnitP9 β).eval z=0) :
    row9G0 ((z⁻¹)^2)+row9G1 ((z⁻¹)^2)*(β/z^3)+row9G2 ((z⁻¹)^2)*(β/z^3)^2-2*(β/z^3)^3=0 := by
  have he : z^9*(row9G0 ((z⁻¹)^2)+row9G1 ((z⁻¹)^2)*(β/z^3)+row9G2 ((z⁻¹)^2)*(β/z^3)^2-2*(β/z^3)^3)=
      1001*(fifthUnitP9 β).eval z := by
    simp only [fifthUnitP9,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    dsimp [row9G0,row9G1,row9G2]
    field_simp <;> ring
  rw [hroot,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 9 hz)



theorem fifth_nonic_derivative (β w : ℂ) :
    (fifthUnitP9 β).derivative.eval w = 9*(w^8-(4/3)*w^6-(8/13)*β*w^5+(20/39)*w^4+(160/429)*β*w^3-(8/143)*w^2+
      (8/143)*β^2*w^2-(16/429)*β*w+1/1287-(2/429)*β^2) := by
  norm_num [fifthUnitP9,derivative_add,derivative_mul,derivative_pow,derivative_X,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  ring




end DerivativeChainPrivate

end


section
-- Source module: Row9BoundP1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_p_coefficient_bounds_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) :
    ∀ i : Fin 32, |row9PCoeffs α i| ≤ row9PBounds1 i := by
  have hm : |α-(115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9PCoeffs,row9PBounds1]
    apply (quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num


end DerivativeChainPrivate

end


section
-- Source module: Row9BoundP2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_p_coefficient_bounds_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    ∀ i : Fin 32, |row9PCoeffs α i| ≤ row9PBounds2 i := by
  have hm : |α-(343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9PCoeffs,row9PBounds2]
    apply (quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num


end DerivativeChainPrivate

end


section
-- Source module: Row9BoundP3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_p_coefficient_bounds_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row9PCoeffs α i| ≤ row9PBounds3 i := by
  have hm : |α-(6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9PCoeffs,row9PBounds3]
    apply (quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num


end DerivativeChainPrivate

end


section
-- Source module: Row9Estimates1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_branch_estimates_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) :
    (7343/5000:ℝ) < α ∧ α < (14687/10000:ℝ) ∧
    (12919/10000:ℝ) < -row9PCoeffs α 1 ∧ -row9PCoeffs α 1 < (323/250:ℝ) ∧
    (19/500:ℝ) < row9PCoeffs α 2 ∧ row9PCoeffs α 2 < (39/1000:ℝ) ∧
    (∑ i : Fin 29, |row9PCoeffs α ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*(10/7:ℝ)^(i.val+1)) ≤ (1/100:ℝ)-1/10000 := by
  have hm : |α-(115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by rw [abs_le]; constructor <;> linarith only [hlo,hhi]
  have h1 := quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1208735622423629499418952264228719406513816544683594454049175222997659701088420003133659669691593545213854420428037114138434202302174347729826924789320826975607213422141378100158124527930769486363094953348789899834609127385374754899487/1646445436884901825725492747514483959849927621152256756112964686326627035323902687953896552562779589866492238404307503135144960636783760662126666655181172598126324502070111324836056335412310150737191410644936315110321864088471929356288) (-1072/2121) (8/2121) hm
  have he1 : (1208735622423629499418952264228719406513816544683594454049175222997659701088420003133659669691593545213854420428037114138434202302174347729826924789320826975607213422141378100158124527930769486363094953348789899834609127385374754899487/1646445436884901825725492747514483959849927621152256756112964686326627035323902687953896552562779589866492238404307503135144960636783760662126666655181172598126324502070111324836056335412310150737191410644936315110321864088471929356288:ℝ)+(-1072/2121)*α+(8/2121)*α^2=row9PCoeffs α 1-(-709016691339832944853191210551429889316088207936040166512641501163356279867470643799458082837912645640522637711796714646628230632756086814122073570835895206482216180152570273097035481460619988825746005790624397033587415433135651040437/548815145628300608575164249171494653283309207050752252037654895442209011774634229317965517520926529955497412801435834378381653545594586887375555551727057532708774834023370441612018778470770050245730470214978771703440621362823976452096) := by
    dsimp [row9PCoeffs]
    ring
  rw [he1] at h1
  norm_num at h1
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have h2 := quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (-2608000917983308080712724399555193068073248144179730839498713087363167224283898769553661246858608574219512494728516864743203301775021757327324948243538127904719341369839624813950808869549060446310499825108635774189858915808853771705376757/51217624650615525994668628389680567023011548438804403169162105462248713814855964816869813957122947481566840552281197807528089435489069226677436346309375917182513702610397023093000040482006144169132550402342678890451892548064184778415407104) (194500/5498339) (-7894/16495017) hm
  have he2 : (-2608000917983308080712724399555193068073248144179730839498713087363167224283898769553661246858608574219512494728516864743203301775021757327324948243538127904719341369839624813950808869549060446310499825108635774189858915808853771705376757/51217624650615525994668628389680567023011548438804403169162105462248713814855964816869813957122947481566840552281197807528089435489069226677436346309375917182513702610397023093000040482006144169132550402342678890451892548064184778415407104:ℝ)+(194500/5498339)*α+(-7894/16495017)*α^2=row9PCoeffs α 2-(659573954889082109815552947151887944118695016211284811832981134298048014577811666323646321054970318201599067940170040367564062526300262613223206056973412011975959347773015254477976980618191970622121874723815021781332339993096738868906663/17072541550205175331556209463226855674337182812934801056387368487416237938285321605623271319040982493855613517427065935842696478496356408892478782103125305727504567536799007697666680160668714723044183467447559630150630849354728259471802368) := by
    dsimp [row9PCoeffs]
    ring
  rw [he2] at h2
  norm_num at h2
  have h2lo := (abs_le.mp h2).1
  have h2hi := (abs_le.mp h2).2
  refine ⟨by linarith only [hlo],by linarith only [hhi],by linarith only [h1lo,h1hi],
    by linarith only [h1lo,h1hi],by linarith only [h2lo,h2hi],by linarith only [h2lo,h2hi],?_⟩
  calc
    _ ≤ ∑ i : Fin 29, row9PBounds1 ⟨i.val+3,by omega⟩ * ((2*i.val+3:ℕ):ℝ)*(10/7:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact row9_p_coefficient_bounds_1 α hlo hhi _
    _ ≤ _ := by norm_num [row9PBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9Estimates2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_branch_estimates_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    (8719/2000:ℝ) < α ∧ α < (10899/2500:ℝ) ∧
    (13447/5000:ℝ) < -row9PCoeffs α 1 ∧ -row9PCoeffs α 1 < (5379/2000:ℝ) ∧
    (33/250:ℝ) < row9PCoeffs α 2 ∧ row9PCoeffs α 2 < (133/1000:ℝ) ∧
    (∑ i : Fin 29, |row9PCoeffs α ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*(10/7:ℝ)^(i.val+1)) ≤ (1/20:ℝ)-1/10000 := by
  have hm : |α-(343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by rw [abs_le]; constructor <;> linarith only [hlo,hhi]
  have h1 := quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1169913526142872343456146989611803447838595886925893788275777729246400304424690410755920778955495905165017863554315812067647275244225747711749519637020539724265553609189922155128187103936803569758578448677221015235089351628726000870437/548815145628300608575164249171494653283309207050752252037654895442209011774634229317965517520926529955497412801435834378381653545594586887375555551727057532708774834023370441612018778470770050245730470214978771703440621362823976452096) (-1072/2121) (8/2121) hm
  have he1 : (1169913526142872343456146989611803447838595886925893788275777729246400304424690410755920778955495905165017863554315812067647275244225747711749519637020539724265553609189922155128187103936803569758578448677221015235089351628726000870437/548815145628300608575164249171494653283309207050752252037654895442209011774634229317965517520926529955497412801435834378381653545594586887375555551727057532708774834023370441612018778470770050245730470214978771703440621362823976452096:ℝ)+(-1072/2121)*α+(8/2121)*α^2=row9PCoeffs α 1-(-4428055030024486365509062336260980604950235739902207410316082468231610051788063160532476915688632107202767083370300466004392315328771155847787854834248477816636095945886099184517543228261501189389878410054746336971421173800210200833135/1646445436884901825725492747514483959849927621152256756112964686326627035323902687953896552562779589866492238404307503135144960636783760662126666655181172598126324502070111324836056335412310150737191410644936315110321864088471929356288) := by
    dsimp [row9PCoeffs]
    ring
  rw [he1] at h1
  norm_num at h1
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have h2 := quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (-7432668265606958377237715326441778460349766386046670528155942057372001243711745292692720820340981702622903620410391083299379272127175982788838568089443420047879989514101436030240332483885198211709685665528548000502808311103191114621293413/51217624650615525994668628389680567023011548438804403169162105462248713814855964816869813957122947481566840552281197807528089435489069226677436346309375917182513702610397023093000040482006144169132550402342678890451892548064184778415407104) (194500/5498339) (-7894/16495017) hm
  have he2 : (-7432668265606958377237715326441778460349766386046670528155942057372001243711745292692720820340981702622903620410391083299379272127175982788838568089443420047879989514101436030240332483885198211709685665528548000502808311103191114621293413/51217624650615525994668628389680567023011548438804403169162105462248713814855964816869813957122947481566840552281197807528089435489069226677436346309375917182513702610397023093000040482006144169132550402342678890451892548064184778415407104:ℝ)+(194500/5498339)*α+(-7894/16495017)*α^2=row9PCoeffs α 2-(2267796404096965541990549922780749741544201096833598041385390790967659354387093840703332845549094694336062776500794779886289385977018337767061079338941842726362842062526952326574484852063571225755183821530452430552315471757875853174212215/17072541550205175331556209463226855674337182812934801056387368487416237938285321605623271319040982493855613517427065935842696478496356408892478782103125305727504567536799007697666680160668714723044183467447559630150630849354728259471802368) := by
    dsimp [row9PCoeffs]
    ring
  rw [he2] at h2
  norm_num at h2
  have h2lo := (abs_le.mp h2).1
  have h2hi := (abs_le.mp h2).2
  refine ⟨by linarith only [hlo],by linarith only [hhi],by linarith only [h1lo,h1hi],
    by linarith only [h1lo,h1hi],by linarith only [h2lo,h2hi],by linarith only [h2lo,h2hi],?_⟩
  calc
    _ ≤ ∑ i : Fin 29, row9PBounds2 ⟨i.val+3,by omega⟩ * ((2*i.val+3:ℕ):ℝ)*(10/7:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact row9_p_coefficient_bounds_2 α hlo hhi _
    _ ≤ _ := by norm_num [row9PBounds2,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9Estimates3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_branch_estimates_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    (390859/5000:ℝ) < α ∧ α < (781719/10000:ℝ) ∧
    (85093/5000:ℝ) < -row9PCoeffs α 1 ∧ -row9PCoeffs α 1 < (170187/10000:ℝ) ∧
    (-43/250:ℝ) < row9PCoeffs α 2 ∧ row9PCoeffs α 2 < (-171/1000:ℝ) ∧
    (∑ i : Fin 29, |row9PCoeffs α ⟨i.val+3,by omega⟩| * ((2*i.val+3:ℕ):ℝ)*(10/7:ℝ)^(i.val+1)) ≤ (3/50:ℝ)-1/10000 := by
  have hm : |α-(6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by rw [abs_le]; constructor <;> linarith only [hlo,hhi]
  have h1 := quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (27101934618943083805026090362463322622515531601362537923029502160645079711897489426836261860793856951364288517277413914053117253888610794937387797558114685265527790432384457986420417484918598437048940387514317686307498547350386257141647/1646445436884901825725492747514483959849927621152256756112964686326627035323902687953896552562779589866492238404307503135144960636783760662126666655181172598126324502070111324836056335412310150737191410644936315110321864088471929356288) (-1072/2121) (8/2121) hm
  have he1 : (27101934618943083805026090362463322622515531601362537923029502160645079711897489426836261860793856951364288517277413914053117253888610794937387797558114685265527790432384457986420417484918598437048940387514317686307498547350386257141647/1646445436884901825725492747514483959849927621152256756112964686326627035323902687953896552562779589866492238404307503135144960636783760662126666655181172598126324502070111324836056335412310150737191410644936315110321864088471929356288:ℝ)+(-1072/2121)*α+(8/2121)*α^2=row9PCoeffs α 1-(-9340083023512984380055570576629630961316659893495687989506083813712496283470493785033658813205333781024000669994922314618189247828234902549975697827100514636455741850233596901851133133789896305721027817179133659191217222088139485121157/548815145628300608575164249171494653283309207050752252037654895442209011774634229317965517520926529955497412801435834378381653545594586887375555551727057532708774834023370441612018778470770050245730470214978771703440621362823976452096) := by
    dsimp [row9PCoeffs]
    ring
  rw [he1] at h1
  norm_num at h1
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have h2 := quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (741166547603825564013840277427125801933775022144433832332304190120736266031295704590746837828954310727115476583171613268323220148232766545117324333788227390957322831506373568479175717128417686050014933485511948729479093656840835367811217/4656147695510502363151693489970960638455595312618582106287464132931701255895996801533619450647540680142440050207381618866189948680824475152494213300852356107501245691854274826636367316546013106284777309303879899131990231642198616219582464) (194500/5498339) (-7894/16495017) hm
  have he2 : (741166547603825564013840277427125801933775022144433832332304190120736266031295704590746837828954310727115476583171613268323220148232766545117324333788227390957322831506373568479175717128417686050014933485511948729479093656840835367811217/4656147695510502363151693489970960638455595312618582106287464132931701255895996801533619450647540680142440050207381618866189948680824475152494213300852356107501245691854274826636367316546013106284777309303879899131990231642198616219582464:ℝ)+(194500/5498339)*α+(-7894/16495017)*α^2=row9PCoeffs α 2-(-266124578089640695618736624539330698696626919367716623019851993205973397178627773366089015145824092048878349494633166351274743509899436408604421143766314944524909529487596615266297297457790275181645408159934004390003997759236749822563035/1552049231836834121050564496656986879485198437539527368762488044310567085298665600511206483549180226714146683402460539622063316226941491717498071100284118702500415230618091608878789105515337702094925769767959966377330077214066205406527488) := by
    dsimp [row9PCoeffs]
    ring
  rw [he2] at h2
  norm_num at h2
  have h2lo := (abs_le.mp h2).1
  have h2hi := (abs_le.mp h2).2
  refine ⟨by linarith only [hlo],by linarith only [hhi],by linarith only [h1lo,h1hi],
    by linarith only [h1lo,h1hi],by linarith only [h2lo,h2hi],by linarith only [h2lo,h2hi],?_⟩
  calc
    _ ≤ ∑ i : Fin 29, row9PBounds3 ⟨i.val+3,by omega⟩ * ((2*i.val+3:ℕ):ℝ)*(10/7:ℝ)^(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact row9_p_coefficient_bounds_3 α hlo hhi _
    _ ≤ _ := by norm_num [row9PBounds3,Fin.sum_univ_succ]
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
-- Source module: FifthOcticScalars

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_scalar_gaps :
    (19/10:ℝ) < (22-3*Real.sqrt 22)/4 ∧ (22-3*Real.sqrt 22)/4 < 2 ∧
    (39/100:ℝ) < (5-4*Real.sqrt 209/19)-(92-9*Real.sqrt 22)/32 ∧
    (3/20:ℝ) < (92-9*Real.sqrt 22)/32-(7/10)*((22-3*Real.sqrt 22)/4) ∧
    (9:ℝ) < (22+3*Real.sqrt 22)/4 ∧ (92+9*Real.sqrt 22)/32 < 17/4 ∧
    (19/10:ℝ) < 5-4*Real.sqrt 209/19 := by
  have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
  have p1 := Real.sqrt_nonneg 22
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have p2 := Real.sqrt_nonneg 209
  have l1 : (46904:ℝ)/10000 < Real.sqrt 22 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 22 < (46905:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (144568:ℝ)/10000 < Real.sqrt 209 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 209 < (144569:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

end


section
-- Source module: FifthNonicUpperData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
theorem fifth_nonic_upper_data (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 7/10 ≤ z.re^2)
    (hroot : (fifthUnitP9 β).eval z=0) :
    ∃ α b : ℝ, ∃ e : ℂ, 1 < α ∧ β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((7343/5000 < α ∧ α < 14687/10000 ∧ 12919/10000 < b ∧ b < 323/250 ∧
          0 < e.re/z.re ∧ e.re/z.re ≤ (49/1000)/(z.re^2+z.im^2) ∧
          -(49/1000)/(z.re^2+z.im^2) ≤ e.im/z.im ∧ e.im/z.im < 0) ∨ (8719/2000 < α ∧ b < 5379/2000 ∧ 0 ≤ e.re/z.re ∧ e.re/z.re ≤ 27/100 ∧
          -(27/100) ≤ e.im/z.im ∧ e.im/z.im ≤ 0) ∨ (78 < α ∧ b < 17019/1000 ∧ -(1/3) ≤ e.re/z.re ∧ e.re/z.re ≤ 0 ∧ 0 ≤ e.im/z.im)) := by
  obtain ⟨a1,a2,a3,Y1,Y2,Y3,⟨hl1,hu1⟩,⟨hl2,hu2⟩,⟨hl3,hu3⟩,
    ⟨hol1,norm1,real1⟩,⟨hol2,norm2,real2⟩,⟨hol3,norm3,real3⟩,hcover⟩ := row9_complete_inverse_branches
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hn : ‖z⁻¹‖^2 ≤ 10/7 := by
    convert inverse_norm_square_bound z (7/10) (by norm_num) hX using 1 <;> norm_num
  have ht : ‖(z⁻¹)^2‖ ≤ 10/7 := by simpa only [norm_pow] using hn
  have heq := fifth_nonic_inverse_equation β z hz hroot
  have hc := hcover ((z⁻¹)^2) ht (β/z^3) (by simpa only [sub_eq_add_neg,neg_mul] using heq)
  let U := z.re^2+z.im^2
  have hU : 7/10 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith only [hU]
  rcases hc with hbranch|hbranch|hbranch
  · let e := newtonRemainder (row9PCoeffs a1) Y1 z
    let b := -row9PCoeffs a1 1
    let γ := row9PCoeffs a1 2
    obtain ⟨hal,hau,hbl,hbu,hgl,hgu,hcoeff⟩ := row9_branch_estimates_1 a1 hl1 hu1
    change _ < b at hbl
    change b < _ at hbu
    change _ < γ at hgl
    change γ < _ at hgu
    have hg := newton_inverse_exact (row9PCoeffs a1) Y1 β z hz hbranch
    have ha0 : row9PCoeffs a1 0=a1 := by norm_num [row9PCoeffs]
    rw [ha0] at hg
    have hgraph : β/z=(a1:ℂ)*z^2-(b:ℂ)+e/z := by simpa only [b,Complex.ofReal_neg,sub_neg_eq_add] using hg
    have herr := newton_error_coordinate_bounds (row9PCoeffs a1) Y1 (10/7) (1/100)
      (by norm_num) hol1 norm1 real1 hcoeff z⁻¹ hn
    obtain ⟨hAl,hAu,hBl,hBu⟩ := inverse_error_coordinate_bounds (newtonError (row9PCoeffs a1) Y1) γ (1/100) z hx hy herr
    change (γ-(1/100))/U ≤ e.re/z.re at hAl
    change e.re/z.re ≤ (γ+(1/100))/U at hAu
    change -(γ+(1/100))/U ≤ e.im/z.im at hBl
    change e.im/z.im ≤ -(γ-(1/100))/U at hBu
    have hlower : -(7/100) ≤ (γ-(1/100))/U := by
      apply (le_div_iff₀ hUp).mpr
      nlinarith only [hU,hgl]
    have hupper : (γ+(1/100))/U ≤ 7/100 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hU,hgu]
    have hAb : e.re/z.re ≤ 7/100 := hAu.trans hupper
    have hBb : -(7/100) ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hBl,hupper]
    have hphase : 0 < (β/z).im := cubic_graph_positive_phase_general β z e a1 b (7/100) (7/10)
      hx hy hX (by norm_num) (by linarith only [hal]) (by linarith only [hal]) hAb hBb hgraph
    have hpos : 0 < (γ-(1/100))/U := div_pos (by linarith only [hgl]) hUp
    have hAp : 0 < e.re/z.re := hpos.trans_le hAl
    have hBn : e.im/z.im < 0 := by
      simp only [neg_div] at hBu
      linarith only [hpos,hBu]
    have hrecip : (γ+(1/100))/U ≤ (49/1000)/U := div_le_div_of_nonneg_right (by linarith only [hgu]) hUp.le
    have hBlo : -(49/1000)/U ≤ e.im/z.im := by
      simp only [neg_div] at hBl ⊢
      linarith only [hBl,hrecip]
    exact ⟨a1,b,e,by linarith only [hal],hgraph,hphase,Or.inl ⟨hal,hau,hbl,hbu,hAp,hAu.trans hrecip,hBlo,hBn⟩⟩
  · let e := newtonRemainder (row9PCoeffs a2) Y2 z
    let b := -row9PCoeffs a2 1
    let γ := row9PCoeffs a2 2
    obtain ⟨hal,hau,hbl,hbu,hgl,hgu,hcoeff⟩ := row9_branch_estimates_2 a2 hl2 hu2
    change _ < b at hbl
    change b < _ at hbu
    change _ < γ at hgl
    change γ < _ at hgu
    have hg := newton_inverse_exact (row9PCoeffs a2) Y2 β z hz hbranch
    have ha0 : row9PCoeffs a2 0=a2 := by norm_num [row9PCoeffs]
    rw [ha0] at hg
    have hgraph : β/z=(a2:ℂ)*z^2-(b:ℂ)+e/z := by simpa only [b,Complex.ofReal_neg,sub_neg_eq_add] using hg
    have herr := newton_error_coordinate_bounds (row9PCoeffs a2) Y2 (10/7) (1/20)
      (by norm_num) hol2 norm2 real2 hcoeff z⁻¹ hn
    obtain ⟨hAl,hAu,hBl,hBu⟩ := inverse_error_coordinate_bounds (newtonError (row9PCoeffs a2) Y2) γ (1/20) z hx hy herr
    change (γ-(1/20))/U ≤ e.re/z.re at hAl
    change e.re/z.re ≤ (γ+(1/20))/U at hAu
    change -(γ+(1/20))/U ≤ e.im/z.im at hBl
    change e.im/z.im ≤ -(γ-(1/20))/U at hBu
    have hlower : -(27/100) ≤ (γ-(1/20))/U := by
      apply (le_div_iff₀ hUp).mpr
      nlinarith only [hU,hgl]
    have hupper : (γ+(1/20))/U ≤ 27/100 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hU,hgu]
    have hAb : e.re/z.re ≤ 27/100 := hAu.trans hupper
    have hBb : -(27/100) ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hBl,hupper]
    have hphase : 0 < (β/z).im := cubic_graph_positive_phase_general β z e a2 b (27/100) (7/10)
      hx hy hX (by norm_num) (by linarith only [hal]) (by linarith only [hal]) hAb hBb hgraph
    have hpos : 0 < (γ-(1/20))/U := div_pos (by linarith only [hgl]) hUp
    have hAp : 0 < e.re/z.re := hpos.trans_le hAl
    have hBn : e.im/z.im < 0 := by
      simp only [neg_div] at hBu
      linarith only [hpos,hBu]
    exact ⟨a2,b,e,by linarith only [hal],hgraph,hphase,Or.inr (Or.inl ⟨by linarith only [hal],by linarith only [hbu],hAp.le,hAb,hBb,hBn.le⟩)⟩
  · let e := newtonRemainder (row9PCoeffs a3) Y3 z
    let b := -row9PCoeffs a3 1
    let γ := row9PCoeffs a3 2
    obtain ⟨hal,hau,hbl,hbu,hgl,hgu,hcoeff⟩ := row9_branch_estimates_3 a3 hl3 hu3
    change _ < b at hbl
    change b < _ at hbu
    change _ < γ at hgl
    change γ < _ at hgu
    have hg := newton_inverse_exact (row9PCoeffs a3) Y3 β z hz hbranch
    have ha0 : row9PCoeffs a3 0=a3 := by norm_num [row9PCoeffs]
    rw [ha0] at hg
    have hgraph : β/z=(a3:ℂ)*z^2-(b:ℂ)+e/z := by simpa only [b,Complex.ofReal_neg,sub_neg_eq_add] using hg
    have herr := newton_error_coordinate_bounds (row9PCoeffs a3) Y3 (10/7) (3/50)
      (by norm_num) hol3 norm3 real3 hcoeff z⁻¹ hn
    obtain ⟨hAl,hAu,hBl,hBu⟩ := inverse_error_coordinate_bounds (newtonError (row9PCoeffs a3) Y3) γ (3/50) z hx hy herr
    change (γ-(3/50))/U ≤ e.re/z.re at hAl
    change e.re/z.re ≤ (γ+(3/50))/U at hAu
    change -(γ+(3/50))/U ≤ e.im/z.im at hBl
    change e.im/z.im ≤ -(γ-(3/50))/U at hBu
    have hlower : -(1/3) ≤ (γ-(3/50))/U := by
      apply (le_div_iff₀ hUp).mpr
      nlinarith only [hU,hgl]
    have hupper : (γ+(3/50))/U ≤ 1/3 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hU,hgu]
    have hAb : e.re/z.re ≤ 1/3 := hAu.trans hupper
    have hBb : -(1/3) ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hBl,hupper]
    have hphase : 0 < (β/z).im := cubic_graph_positive_phase_general β z e a3 b (1/3) (7/10)
      hx hy hX (by norm_num) (by linarith only [hal]) (by linarith only [hal]) hAb hBb hgraph
    have hneg : (γ+3/50)/U < 0 := div_neg_of_neg_of_pos (by linarith only [hgu]) hUp
    have hAn : e.re/z.re ≤ 0 := (hAu.trans hneg.le)
    have hBp : 0 ≤ e.im/z.im := by
      simp only [neg_div] at hBl
      linarith only [hneg,hBl]
    exact ⟨a3,b,e,by linarith only [hal],hgraph,hphase,Or.inr (Or.inr ⟨by linarith only [hal],by linarith only [hbu],hlower.trans hAl,hAn,hBp⟩)⟩
end DerivativeChainPrivate

end


section
-- Source module: FifthMiddleBounds

set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fifth_octic_selected_bounds (β z : ℂ) (hR : 0 ≤ β.re) (hx : 0 < z.re) (hy : 0 < z.im)
    (hX : 3/5 ≤ z.re^2)
    (hg : β/z = (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z) :
    7/10 < z.re^2 ∧ (fifthOcticRemainder z).re/z.re ≤ 13/100 ∧
      (fifthOcticRemainder z).im/z.im ≤ 0 ∧
      (3*((fifthOcticRemainder z).re/z.re)-(fifthOcticRemainder z).im/z.im)/2 ≤ 13/50 ∧
      7/10 ≤ z.re^2-3*z.im^2 := by
  let α := (22-3*Real.sqrt 22)/4
  let b := (92-9*Real.sqrt 22)/32
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hr := (cubic_graph_coordinate_parts β z (fifthOcticRemainder z) α b hz hg).1
  have hRp : β.re/z.re = α*(z.re^2-3*z.im^2)-b+(fifthOcticRemainder z).re/z.re := by rw [hr]; field_simp
  have hR0 : 0 ≤ β.re/z.re := div_nonneg hR hx.le
  rw [hRp] at hR0
  obtain ⟨ha,_,_,hslack,_,_,_⟩ := fifth_octic_scalar_gaps
  change (19/10:ℝ) < α at ha
  change (3/20:ℝ) < b-(7/10)*α at hslack
  have hterm := mul_nonneg (show 0 ≤ α by linarith only [ha]) (sq_nonneg z.im)
  have hUp : 0 < z.re^2+z.im^2 := by positivity
  obtain ⟨_,hA,hB,hBn⟩ := fifth_octic_remainder_bounds z hx hy hX
  have hU : 3/5 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hA1 : (fifthOcticRemainder z).re/z.re ≤ 3/20 := by
    apply hA.trans
    apply (div_le_iff₀ hUp).mpr
    linarith only [hU]
  have hX1 : 7/10 < z.re^2 := by
    have ht : α*(7/10) < α*z.re^2 := by nlinarith only [hR0,hterm,hA1,hslack]
    exact lt_of_mul_lt_mul_left ht (by linarith only [ha])
  have hc : (9/100:ℝ)/(z.re^2+z.im^2) ≤ 13/100 := by
    apply (div_le_iff₀ hUp).mpr
    nlinarith only [hX1,sq_nonneg z.im]
  refine ⟨hX1,hA.trans hc,hBn.le,?_,?_⟩
  · simp only [neg_div] at hB
    linarith only [hA,hB,hc]
  · have ht : α*(7/10) < α*(z.re^2-3*z.im^2) := by linarith only [hR0,hA1,hslack]
    exact (lt_of_mul_lt_mul_left ht (by linarith only [ha])).le
end DerivativeChainPrivate

end


section
-- Source module: FifthNonicPhase

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_nonic_real_root_parameter (β : ℂ) (x : ℝ) (hx : 0 < x) (hX : 7/10 ≤ x^2)
    (hroot : (fifthUnitP9 β).eval (x:ℂ)=0) : β.im=0 := by
  obtain ⟨a1,a2,a3,Y1,Y2,Y3,_,_,_,⟨_,_,real1⟩,⟨_,_,real2⟩,⟨_,_,real3⟩,hcover⟩ := row9_complete_inverse_branches
  have hz : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hn : ‖(x:ℂ)⁻¹‖^2 ≤ 10/7 := by
    convert inverse_norm_square_bound (x:ℂ) (7/10) (by norm_num) (by simpa using hX) using 1 <;> norm_num
  have ht : ((x:ℂ)⁻¹)^2=(((x⁻¹)^2:ℝ):ℂ) := by norm_cast
  have hs : |(x⁻¹)^2| ≤ 10/7 := by
    have hh : ‖((x:ℂ)⁻¹)^2‖ ≤ 10/7 := by simpa only [norm_pow] using hn
    rw [ht] at hh
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hh
  have htc : ‖(((x⁻¹)^2:ℝ):ℂ)‖ ≤ 10/7 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hs
  have hs2 : |(x⁻¹)^2| ≤ 2 := by linarith only [hs]
  have heq := fifth_nonic_inverse_equation β (x:ℂ) hz hroot
  rw [ht] at heq
  have hc := hcover (((x⁻¹)^2:ℝ):ℂ) htc (β/(x:ℂ)^3) (by simpa only [sub_eq_add_neg,neg_mul] using heq)
  have him : (β/(x:ℂ)^3).im=0 := by
    rcases hc with h|h|h
    · rw [h]
      exact real_newton_branch_value (row9PCoeffs a1) Y1 _ (real1 _ hs2)
    · rw [h]
      exact real_newton_branch_value (row9PCoeffs a2) Y2 _ (real2 _ hs2)
    · rw [h]
      exact real_newton_branch_value (row9PCoeffs a3) Y3 _ (real3 _ hs2)
  simpa [Complex.div_im,← Complex.ofReal_pow,hx.ne'] using him

theorem fifth_nonic_nonnegative_im (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 7/10 ≤ z.re^2) (hroot : (fifthUnitP9 β).eval z=0) :
    0 ≤ z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0 ≤ z.im := by
    by_contra hn
    have hy : z.im < 0 := lt_of_not_ge hn
    have hroot' : (fifthUnitP9 (starRingEnd ℂ β)).eval (starRingEnd ℂ z)=0 := by
      simpa [fifthUnitP9,map_ofNat] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_nonic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
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
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_nonic_upper_data β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    exact fifth_nonic_real_root_parameter β z.re hx hX hroot
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 7/10 ≤ w.re^2)
    (hwroot : w^8-(4/3)*w^6-(8/13)*β*w^5+(20/39)*w^4+(160/429)*β*w^3-(8/143)*w^2+
      (8/143)*β^2*w^2-(16/429)*β*w+1/1287-(2/429)*β^2=0)
    (hwinv : β/w=(((22-3*Real.sqrt 22)/4:ℝ):ℂ)*w^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder w/w) :
    ∃ z : ℂ, ∃ α b : ℝ, ∃ e : ℂ,
      (fifthUnitP9 β).eval z=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧ 4/5 < z.re^2 ∧
      7343/5000 < α ∧ α < 14687/10000 ∧ 12919/10000 < b ∧ b < 323/250 ∧
      β/z=(α:ℂ)*z^2-(b:ℂ)+e/z ∧ e.re/z.re ≤ 1/16 ∧ e.im/z.im ≤ 0 ∧
      (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/8 ∧ 4/5 ≤ z.re^2-3*z.im^2 := by
  let α₀ := (22-3*Real.sqrt 22)/4
  let b₀ := (92-9*Real.sqrt 22)/32
  let E₀ := fifthOcticRemainder w
  obtain ⟨hα₀lo,hα₀up,_,_,_,_,_⟩ := fifth_octic_scalar_gaps
  change (19/10:ℝ) < α₀ at hα₀lo
  change α₀ < 2 at hα₀up
  have hb₀lo : (7779/5000:ℝ) < b₀ := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 22)
    have hp := Real.sqrt_nonneg 22
    dsimp [b₀]
    nlinarith only [hs,hp]
  obtain ⟨_,hA₀,hB₀,hC₀,hW₀⟩ := fifth_octic_selected_bounds β w hR hwpos hwim (by linarith only [hwX]) hwinv
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  obtain ⟨hr₀,hi₀,_⟩ := cubic_graph_coordinate_parts β w E₀ α₀ b₀ hw hwinv
  have hR₀ : β.re/w.re=α₀*(w.re^2-3*w.im^2)-b₀+E₀.re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im=α₀*(3*w.re^2-w.im^2)-b₀+E₀.im/w.im := by rw [hi₀]; field_simp
  have hcritical : (fifthUnitP9 β).derivative.eval w=0 := by rw [fifth_nonic_derivative,hwroot,mul_zero]
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent (fifthUnitP9 β) (by rw [fifth_unit_p9_degree]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 7/10 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  obtain ⟨hy0,hzero⟩ := fifth_nonic_nonnegative_im β z hR hI.le hx hX hz
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith only [this,hI]
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fifth_nonic_upper_data β z hx hy hX hz
  obtain ⟨hr₁,hi₁,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re=α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im=α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  rcases hcases with hs|hmid|hhigh
  · obtain ⟨hal,hau,hbl,hbu,hAp,hAr,hBr,hBn⟩ := hs
    have hC₁ : 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2 := by linarith only [hAp,hBn]
    have himorder : w.im ≤ z.im := by
      by_contra hn
      exact inverse_graph_southeast_impossible α₀ α b₀ b (E₀.re/w.re) (e.re/z.re)
        (E₀.im/w.im) (e.im/z.im) (13/50) β.re β.im w.re w.im z.re z.im
        (by linarith only [hal]) (by linarith only [hau,hα₀lo]) hwpos hy hxz (le_of_not_ge hn)
        hR hI.le hC₀ hC₁ (by linarith only [hb₀lo,hbu]) hR₀ hI₀ hR₁ hI₁
    have hU : 7/10 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
    have hUp : 0 < z.re^2+z.im^2 := by linarith only [hU]
    have hAu : e.re/z.re ≤ 7/100 := by
      apply hAr.trans
      apply (div_le_iff₀ hUp).mpr
      linarith only [hU]
    have hRR : 0 ≤ α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [← hR₁]; positivity
    have hterm := mul_nonneg (show 0 ≤ α by linarith only [hal]) (sq_nonneg z.im)
    have hXnew : 4/5 < z.re^2 := by
      have ht : α*(4/5) < α*z.re^2 := by nlinarith only [hRR,hAu,hbl,hau,hterm]
      exact lt_of_mul_lt_mul_left ht (by linarith only [hal])
    have hc : (49/1000:ℝ)/(z.re^2+z.im^2) ≤ 1/16 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hXnew,sq_nonneg z.im]
    have hW : 4/5 ≤ z.re^2-3*z.im^2 := by
      have ht : α*(4/5) < α*(z.re^2-3*z.im^2) := by linarith only [hRR,hAu,hbl,hau]
      exact (lt_of_mul_lt_mul_left ht (by linarith only [hal])).le
    refine ⟨z,α,b,e,hz,hxz,himorder,hXnew,hal,hau,hbl,hbu,hgraph,hAr.trans hc,hBn.le,?_,hW⟩
    simp only [neg_div] at hBr
    linarith only [hAr,hBr,hc]
  · exfalso
    obtain ⟨hfast,hb,hAlo,hAhi,hBlo,hBhi⟩ := hmid
    by_cases hvy : z.im ≤ w.im
    · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ α b₀ b
        (E₀.re/w.re) (e.re/z.re) (7/10) (13/100) 0 hR hwpos hy.le hxz hvy hW₀
        (by linarith only [hfast]) (by linarith only [hfast,hα₀up]) hA₀ hAlo
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hR₀ hR₁
    · exact fast_graph_northeast_impossible α₀ α b₀ b (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
        (7/10) (9/25) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
        hR hI.le hwX (by linarith only [hα₀lo]) (by linarith only [hfast])
        (by linarith only [hfast,hα₀up]) hB₀ (by linarith only [hBlo,hAhi])
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hI₀ hR₁ hI₁
  · exfalso
    obtain ⟨hfast,hb,hAlo,hAhi,hBlo⟩ := hhigh
    by_cases hvy : z.im ≤ w.im
    · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ α b₀ b
        (E₀.re/w.re) (e.re/z.re) (7/10) (13/100) (-(1/3)) hR hwpos hy.le hxz hvy hW₀
        (by linarith only [hfast]) (by linarith only [hfast,hα₀up]) hA₀ hAlo
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hR₀ hR₁
    · exact fast_graph_northeast_impossible α₀ α b₀ b (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
        (7/10) 0 β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
        hR hI.le hwX (by linarith only [hα₀lo]) (by linarith only [hfast])
        (by linarith only [hfast,hα₀up]) hB₀ (by linarith only [hBlo,hAhi])
        (by linarith only [hfast,hα₀up,hb,hb₀lo]) hI₀ hR₁ hI₁
