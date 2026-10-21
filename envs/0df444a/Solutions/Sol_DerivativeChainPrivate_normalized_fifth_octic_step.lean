-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_octic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T18:53:52.023621+00:00
-- url     : https://prove2.me/submissions/a6f5031a-cb5b-45fc-941c-93c0e1890929

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










theorem fifth_octic_sqrt_remainder_identity (u : ℂ) :
    fifthOcticRadicand u-(fifthOcticPoly u)^2 = u^17*fifthOcticResidual u := by
  norm_num [fifthOcticRadicand,fifthOcticPoly,fifthOcticResidual,fifthOcticCoeffs,fifthOcticResidualCoeffs,Fin.sum_univ_succ]
  ring

theorem fifth_octic_expansion_identity (u : ℂ) :
    (11/2)-(10/3)*u+(1/3)*u^2-((3*Real.sqrt 22/4:ℝ):ℂ)*(1-u/3)*fifthOcticPoly u-
      ((((22-3*Real.sqrt 22)/4:ℝ):ℂ)-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)*u)*(1-u/12) =
    u^2*((1-u/12)*(∑ i : Fin 15, (fifthOcticExpansionCoeffs i:ℂ)*u^i.val)+u^15*(fifthOcticRationalTailCoeff:ℂ)) := by
  norm_num [fifthOcticPoly,fifthOcticCoeffs,fifthOcticExpansionCoeffs,fifthOcticRationalTailCoeff,Fin.sum_univ_succ]
  push_cast
  ring

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
-- Source module: FifthOcticPoleBounds


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_pole_corrections (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 3/5 ≤ z.re^2) :
    let U := z.re^2+z.im^2
    let E := (3/16)*z/(z^2-1/12)
    (3/25)/U ≤ E.re/z.re ∧ E.re/z.re ≤ (9/40)/U ∧
      -(3/10)/U ≤ E.im/z.im ∧ E.im/z.im ≤ -(4/25)/U := by
  let U := z.re^2+z.im^2
  let D := ‖z^2-(1/12:ℂ)‖^2
  let E := (3/16:ℂ)*z/(z^2-1/12)
  have hU : 3/5 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
  have hUp : 0 < U := by linarith
  have hUc : 0 < U-1/12 := by linarith
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hpole : z^2-(1/12:ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    nlinarith only [hi,hx,hy]
  obtain ⟨hr,hi,_,hd⟩ := rational_inverse_parts E z 0 0 (3/16) (1/12) hz (by norm_num; exact hpole)
    (by dsimp [E]; norm_num; field_simp)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,zero_mul,sub_zero,zero_add,zero_sub] at hr hi hd
  have hDlo : (U-1/12)^2 ≤ D := by
    dsimp only [D,U]
    nlinarith only [hd,sq_nonneg z.im]
  have hDhi : D ≤ (U+1/12)^2 := by
    dsimp only [D,U]
    nlinarith only [hd,sq_nonneg z.re]
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hUc) hDlo
  have hAr : E.re/z.re = (3/16:ℝ)*(U-1/12)/D := by
    rw [hr]
    dsimp [U,D]
    field_simp
  have hBi : E.im/z.im = -(3/16:ℝ)*(U+1/12)/D := by
    rw [hi]
    dsimp [U,D]
    field_simp <;> ring
  have hAlo : (3/25:ℝ)/U ≤ (3/16)*(U-1/12)/D := by
    apply (div_le_div_iff₀ hUp hDp).mpr
    nlinarith [sq_nonneg (U-3/5)]
  have hAhi : (3/16:ℝ)*(U-1/12)/D ≤ (9/40)/U := by
    apply (div_le_div_iff₀ hDp hUp).mpr
    nlinarith [sq_nonneg (U-3/5)]
  have hBlo : (4/25:ℝ)/U ≤ (3/16)*(U+1/12)/D := by
    apply (div_le_div_iff₀ hUp hDp).mpr
    nlinarith [sq_nonneg (U-3/5)]
  have hBhi : (3/16:ℝ)*(U+1/12)/D ≤ (3/10)/U := by
    apply (div_le_div_iff₀ hDp hUp).mpr
    nlinarith [sq_nonneg (U-3/5)]
  change (3/25:ℝ)/U ≤ E.re/z.re ∧ _
  rw [hAr,hBi]
  simp only [neg_mul,neg_div]
  exact ⟨hAlo,hAhi,by linarith,by linarith⟩

end DerivativeChainPrivate

end


section
-- Source module: FifthOcticInverse


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem fifth_octic_sqrt_exact_remainder (u : ℂ) (hu : ‖u‖ ≤ 9/4) :
    Complex.sqrt (fifthOcticRadicand u) = fifthOcticPoly u+
      u^17*fifthOcticResidual u/(Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u) := by
  have hd := (fifth_octic_denominator_bound u hu).1
  have hs : (Complex.sqrt (fifthOcticRadicand u))^2 = fifthOcticRadicand u :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have he : (Complex.sqrt (fifthOcticRadicand u)-fifthOcticPoly u)*
      (Complex.sqrt (fifthOcticRadicand u)+fifthOcticPoly u) = u^17*fifthOcticResidual u := by
    calc
      _ = (Complex.sqrt (fifthOcticRadicand u))^2-(fifthOcticPoly u)^2 := by ring
      _ = _ := by rw [hs,fifth_octic_sqrt_remainder_identity]
  have hh := (eq_div_iff hd).mpr he
  linear_combination hh

theorem fifth_octic_polynomial_error_identity (w : ℂ) :
    (fifthOcticLeadingError:ℂ)*w+fifthOcticPolynomialError w =
      w*(∑ i : Fin 15, (fifthOcticExpansionCoeffs i:ℂ)*(w^2)^i.val) := by
  norm_num [fifthOcticLeadingError,fifthOcticPolynomialError,fifthOcticExpansionCoeffs,fifthOcticErrorCoeffs,Fin.sum_univ_succ]
  ring

theorem fifth_octic_remainder_scaled (w : ℂ) (hw : ‖w^2‖ ≤ 9/4) :
    w^3*(1-(1/12)*w^2)*((fifthOcticLeadingError:ℂ)*w+fifthOcticError w) =
      (11/2)-(10/3)*w^2+(1/3)*w^4-
      ((3*Real.sqrt 22/4:ℝ):ℂ)*(1-(1/3)*w^2)*Complex.sqrt (fifthOcticRadicand (w^2))-
      ((((22-3*Real.sqrt 22)/4:ℝ):ℂ)-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)*w^2)*(1-(1/12)*w^2) := by
  have hp := (fifth_octic_pole_bound (w^2) hw).1
  have hs := fifth_octic_sqrt_exact_remainder (w^2) hw
  have he : Complex.sqrt (fifthOcticRadicand (w^2))-fifthOcticPoly (w^2) =
      (w^2)^17*fifthOcticResidual (w^2)/(Complex.sqrt (fifthOcticRadicand (w^2))+fifthOcticPoly (w^2)) := by
    linear_combination hs
  have htail : (1-(1/12:ℂ)*w^2)*fifthOcticTail w =
      (fifthOcticRationalTailCoeff:ℂ)*w^31-
      ((3*Real.sqrt 22/4:ℝ):ℂ)*w^31*(1-(1/3:ℂ)*w^2)*fifthOcticResidual (w^2)/
        (Complex.sqrt (fifthOcticRadicand (w^2))+fifthOcticPoly (w^2)) := by
    unfold fifthOcticTail
    rw [mul_sub,← mul_div_assoc,← mul_div_assoc,
      mul_div_cancel_left₀ _ hp,mul_div_cancel_left₀ _ hp]
  calc
    _ = (w^2)^2*((1-(1/12)*w^2)*(∑ i : Fin 15, (fifthOcticExpansionCoeffs i:ℂ)*(w^2)^i.val)+
          (w^2)^15*(fifthOcticRationalTailCoeff:ℂ))-
        ((3*Real.sqrt 22/4:ℝ):ℂ)*(1-(1/3)*w^2)*
          (Complex.sqrt (fifthOcticRadicand (w^2))-fifthOcticPoly (w^2)) := by
      unfold fifthOcticError
      rw [← add_assoc,fifth_octic_polynomial_error_identity,he]
      linear_combination w^3*htail
    _ = _ := by linear_combination -(fifth_octic_expansion_identity (w^2))

theorem fifth_octic_inverse_exact (z : ℂ) (hz : z ≠ 0) (hn : ‖z⁻¹‖^2 ≤ 5/3) :
    (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z =
      ((11/2)*z^4-(10/3)*z^2+1/3-
        ((3*Real.sqrt 22/4:ℝ):ℂ)*z^2*(z^2-1/3)*Complex.sqrt (fifthOcticRadicand ((z⁻¹)^2)))/(z^2-1/12) := by
  have hw : ‖(z⁻¹)^2‖ ≤ 9/4 := by rw [norm_pow]; linarith
  have hp := (fifth_octic_pole_bound ((z⁻¹)^2) hw).1
  have hzpole : z^2-(1/12:ℂ) ≠ 0 := by
    intro he
    apply hp
    field_simp
    linear_combination (12:ℂ)*he
  have hS := fifth_octic_remainder_scaled z⁻¹ hw
  change (z⁻¹)^3*(1-(1/12)*(z⁻¹)^2)*fifthOcticRemainder z = _ at hS
  apply (eq_div_iff hzpole).mpr
  calc
    _ = ((((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z)*(z^2-1/12)-
        z^4*((z⁻¹)^3*(1-(1/12)*(z⁻¹)^2)*fifthOcticRemainder z-
          ((11/2)-(10/3)*(z⁻¹)^2+(1/3)*(z⁻¹)^4-
          ((3*Real.sqrt 22/4:ℝ):ℂ)*(1-(1/3)*(z⁻¹)^2)*Complex.sqrt (fifthOcticRadicand ((z⁻¹)^2))-
          ((((22-3*Real.sqrt 22)/4:ℝ):ℂ)-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)*(z⁻¹)^2)*(1-(1/12)*(z⁻¹)^2))) := by
      rw [hS]
      ring
    _ = _ := by field_simp; ring

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
-- Source module: FifthOcticGraphs

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_upper_graphs (β z : ℂ) (hx : 0 < z.re) (hX : 3/5 ≤ z.re^2)
    (hroot : z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
      (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0) :
    β/z = (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z ∨
    β/z = (((22+3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92+9*Real.sqrt 22)/32:ℝ):ℂ)+
      ((3/16)*z/(z^2-1/12)-fifthOcticRemainder z)/z := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hnorm : 3/5 ≤ ‖z‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  have hn : ‖z⁻¹‖^2 ≤ 5/3 := by
    rw [norm_inv,inv_pow]
    apply (inv_le_comm₀ (by positivity : 0 < ‖z‖^2) (by norm_num)).mpr
    norm_num
    exact hnorm
  have hu : ‖(z⁻¹)^2‖ ≤ 9/4 := by rw [norm_pow]; linarith
  have hpole := (fifth_octic_pole_bound ((z⁻¹)^2) hu).1
  have hzp : z^2-(1/12:ℂ) ≠ 0 := by
    intro he
    apply hpole
    field_simp
    linear_combination (12:ℂ)*he
  let S := Complex.sqrt (fifthOcticRadicand ((z⁻¹)^2))
  let s : ℂ := (Real.sqrt 22:ℂ)
  have hs : s^2=22 := by dsimp [s]; rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hS : S^2=fifthOcticRadicand ((z⁻¹)^2) := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hd : (β*(z^2-1/12)-z*((11/2)*z^4-(10/3)*z^2+1/3))^2 =
      (99/8)*(z^2-1/3)^2*(z^6-z^4/4+z^2/66+1/1188) := by
    linear_combination (143/8)*(z^2-1/12)*hroot
  have hsquare : ((3/4)*s*z^3*(z^2-1/3)*S)^2 =
      (99/8)*(z^2-1/3)^2*(z^6-z^4/4+z^2/66+1/1188) := by
    calc
      _ = (9/16)*s^2*z^6*(z^2-1/3)^2*S^2 := by ring
      _ = _ := by rw [hs,hS]; unfold fifthOcticRadicand; field_simp <;> ring
  have hsplit := (sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  have hbase : β/z = ((11/2)*z^4-(10/3)*z^2+1/3-(3*s/4)*z^2*(z^2-1/3)*S)/(z^2-1/12) ∨
      β/z = ((11/2)*z^4-(10/3)*z^2+1/3+(3*s/4)*z^2*(z^2-1/3)*S)/(z^2-1/12) := by
    rcases hsplit with hp|hm
    · right
      apply (div_eq_div_iff hz hzp).mpr
      linear_combination hp
    · left
      apply (div_eq_div_iff hz hzp).mpr
      linear_combination hm
  have hminus := fifth_octic_inverse_exact z hz hn
  have hplus : (((22+3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92+9*Real.sqrt 22)/32:ℝ):ℂ)+
      ((3/16)*z/(z^2-1/12)-fifthOcticRemainder z)/z =
      ((11/2)*z^4-(10/3)*z^2+1/3+(3*s/4)*z^2*(z^2-1/3)*S)/(z^2-1/12) := by
    calc
      _ = 11*z^2-23/4+(3/16)/(z^2-1/12)-
          ((((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z) := by
        push_cast
        field_simp <;> ring
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
-- Source module: FifthOcticUpperData


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_upper_data (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 3/5 ≤ z.re^2)
    (hroot : z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
      (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0) :
    ∃ α b : ℝ, ∃ e : ℂ, 19/10 < α ∧ β/z = (α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((α = (22-3*Real.sqrt 22)/4 ∧ b = (92-9*Real.sqrt 22)/32 ∧ e = fifthOcticRemainder z ∧
          0 ≤ (3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α = (22+3*Real.sqrt 22)/4 ∧ b = (92+9*Real.sqrt 22)/32 ∧
          0 ≤ e.re/z.re ∧ e.re/z.re ≤ 3/8 ∧ -(1/2) ≤ e.im/z.im ∧ e.im/z.im ≤ 0)) := by
  obtain ⟨hAp,hAr,hBr,hBn⟩ := fifth_octic_remainder_bounds z hx hy hX
  obtain ⟨hαm,_,_,_,hαp,_,_⟩ := fifth_octic_scalar_gaps
  have hU : 3/5 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hUp : 0 < z.re^2+z.im^2 := by linarith
  have hsmall : (9/100:ℝ)/(z.re^2+z.im^2) ≤ 3/20 := by
    apply (div_le_iff₀ hUp).mpr
    linarith only [hU]
  have hAu : (fifthOcticRemainder z).re/z.re ≤ 3/20 := hAr.trans hsmall
  have hBl : -(3/20) ≤ (fifthOcticRemainder z).im/z.im := by
    rw [neg_div] at hBr
    linarith only [hBr,hsmall]
  have hCp : 0 < (3*((fifthOcticRemainder z).re/z.re)-(fifthOcticRemainder z).im/z.im)/2 := by linarith only [hAp,hBn]
  rcases fifth_octic_upper_graphs β z hx hX hroot with hm|hp
  · refine ⟨(22-3*Real.sqrt 22)/4,(92-9*Real.sqrt 22)/32,fifthOcticRemainder z,hαm,hm,?_,
      Or.inl ⟨rfl,rfl,rfl,hCp.le⟩⟩
    exact cubic_graph_positive_phase_general β z (fifthOcticRemainder z) _ _ (3/20) (3/5)
      hx hy hX (by norm_num) (by linarith only [hαm]) (by linarith only [hαm]) hAu hBl hm
  · let U := z.re^2+z.im^2
    let P := (3/16:ℂ)*z/(z^2-1/12)
    let E := P-fifthOcticRemainder z
    obtain ⟨hPAl,hPAu,hPBl,hPBu⟩ := fifth_octic_pole_corrections z hx hy hX
    change (3/25:ℝ)/U ≤ P.re/z.re at hPAl
    change P.re/z.re ≤ (9/40:ℝ)/U at hPAu
    change -(3/10:ℝ)/U ≤ P.im/z.im at hPBl
    change P.im/z.im ≤ -(4/25:ℝ)/U at hPBu
    change (fifthOcticRemainder z).re/z.re ≤ (9/100:ℝ)/U at hAr
    change -(9/100:ℝ)/U ≤ (fifthOcticRemainder z).im/z.im at hBr
    have hU : 3/5 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
    have hUp : 0 < U := by linarith
    have hArat : E.re/z.re = P.re/z.re-(fifthOcticRemainder z).re/z.re := by simp only [E,Complex.sub_re,sub_div]
    have hBrat : E.im/z.im = P.im/z.im-(fifthOcticRemainder z).im/z.im := by simp only [E,Complex.sub_im,sub_div]
    have hcmpA : (9/100:ℝ)/U ≤ (3/25:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hcmpB : (9/100:ℝ)/U ≤ (4/25:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hboundA : (9/40:ℝ)/U ≤ 3/8 := by apply (div_le_iff₀ hUp).mpr; linarith
    have hboundB : (3/10:ℝ)/U ≤ 1/2 := by apply (div_le_iff₀ hUp).mpr; linarith
    simp only [neg_div] at hPBl hPBu hBr
    have hA0 : 0 ≤ E.re/z.re := by rw [hArat]; linarith
    have hA1 : E.re/z.re ≤ 3/8 := by rw [hArat]; linarith
    have hB0 : -(1/2) ≤ E.im/z.im := by rw [hBrat]; linarith
    have hB1 : E.im/z.im ≤ 0 := by rw [hBrat]; linarith
    refine ⟨(22+3*Real.sqrt 22)/4,(92+9*Real.sqrt 22)/32,E,by linarith,hp,?_,
      Or.inr ⟨rfl,rfl,hA0,hA1,hB0,hB1⟩⟩
    exact cubic_graph_positive_phase_general β z E _ _ (1/2) (3/5) hx hy hX
      (by norm_num) (by linarith only [hαp]) (by linarith only [hαp]) (by linarith only [hA1]) hB0 hp
end DerivativeChainPrivate

end


section
-- Source module: FifthOcticPhase

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_octic_nonnegative_im (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 3/5 ≤ z.re^2)
    (hroot : z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
      (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0) :
    0 ≤ z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0 ≤ z.im := by
    by_contra hn
    have hy : z.im < 0 := lt_of_not_ge hn
    have hroot' : (starRingEnd ℂ z)^8-(4/3)*(starRingEnd ℂ z)^6-(8/13)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^5+
        (20/39)*(starRingEnd ℂ z)^4+(160/429)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^3-(8/143)*(starRingEnd ℂ z)^2+
        (8/143)*(starRingEnd ℂ β)^2*(starRingEnd ℂ z)^2-(16/429)*(starRingEnd ℂ β)*(starRingEnd ℂ z)+
        1/1287-(2/429)*(starRingEnd ℂ β)^2=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero,map_one] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_octic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
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
    obtain ⟨α,b,e,_,_,hp,_⟩ := fifth_octic_upper_data β z hx hy hX hroot
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
      exact (inv_le_comm₀ (sq_pos_of_pos hx) (by norm_num)).mpr (by norm_num; linarith only [hX])
    have heIm : (fifthOcticRemainder (z.re:ℂ)).im=0 := by
      unfold fifthOcticRemainder
      rw [← Complex.ofReal_inv,Complex.add_im,(fifth_octic_error_axes _ hn).1]
      simp
    rcases fifth_octic_upper_graphs β (z.re:ℂ) (by simpa using hx) (by simpa using hX) hroot with hm|hp
    · have hi := congrArg Complex.im hm
      simp [Complex.div_im,heIm,← Complex.ofReal_pow] at hi
      exact hi.resolve_right hx.ne'
    · have hi := congrArg Complex.im hp
      simp [Complex.div_im,heIm,← Complex.ofReal_pow] at hi
      exact hi.resolve_right hx.ne'

end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 3/5 ≤ w.re^2)
    (hwroot : (2/143)*β^2*w-(5/13)*β*w^4+(20/143)*β*w^2-(2/429)*β+
      w^7-w^5+(10/39)*w^3-(2/143)*w=0)
    (hwinv : β/w = (((55-3*Real.sqrt 209)/4:ℝ):ℂ)*w^2-((5-4*Real.sqrt 209/19:ℝ):ℂ)+fifthSepticRemainder w/w)
    (hA₀hi : (fifthSepticRemainder w).re/w.re ≤ 39/200)
    (hB₀hi : (fifthSepticRemainder w).im/w.im ≤ 0)
    (hC₀ : (3*((fifthSepticRemainder w).re/w.re)-(fifthSepticRemainder w).im/w.im)/2 ≤ 39/100)
    (hWedge : 3/5 ≤ w.re^2-3*w.im^2) :
    ∃ z : ℂ,
      z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
        (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧
      β/z = (((22-3*Real.sqrt 22)/4:ℝ):ℂ)*z^2-(((92-9*Real.sqrt 22)/32:ℝ):ℂ)+fifthOcticRemainder z/z := by
  let α₀ := (55-3*Real.sqrt 209)/4
  let b₀ := 5-4*Real.sqrt 209/19
  let E₀ := fifthSepticRemainder w
  obtain ⟨hαm,hαmup,hgap,_,hαp,hbfast,hb₀lo⟩ := fifth_octic_scalar_gaps
  have hα₀lo := fifth_septic_scalar_gaps.1
  have hα₀up := fifth_septic_scalar_gaps.2.1
  change (29/10:ℝ) < α₀ at hα₀lo
  change α₀ < 3 at hα₀up
  change (19/10:ℝ) < b₀ at hb₀lo
  have hα₀ : 0 < α₀ := by linarith only [hα₀lo]
  have hαm7 : (22-3*Real.sqrt 22)/4 < α₀ := by linarith only [hαmup,hα₀lo]
  have hα7p : α₀ < (22+3*Real.sqrt 22)/4 := by linarith only [hαp,hα₀up]
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  obtain ⟨hr₀,hi₀,_⟩ := cubic_graph_coordinate_parts β w E₀ α₀ b₀ hw hwinv
  have hR₀ : β.re/w.re = α₀*(w.re^2-3*w.im^2)-b₀+E₀.re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im = α₀*(3*w.re^2-w.im^2)-b₀+E₀.im/w.im := by rw [hi₀]; field_simp
  let p : Polynomial ℂ := X^8-C (4/3)*X^6-C ((8/13)*β)*X^5+C (20/39)*X^4+
    C ((160/429)*β)*X^3+C ((8/143)*β^2-8/143)*X^2-C ((16/429)*β)*X+C (1/1287-(2/429)*β^2)
  have hpdeg : p.natDegree=8 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w=0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 8*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 3/5 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hzroot : z^8-(4/3)*z^6-(8/13)*β*z^5+(20/39)*z^4+(160/429)*β*z^3-(8/143)*z^2+
      (8/143)*β^2*z^2-(16/429)*β*z+1/1287-(2/429)*β^2=0 := by
    have he := hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at he
    linear_combination he
  obtain ⟨hy0,hzero⟩ := fifth_octic_nonnegative_im β z hR hI.le hx hX hzroot
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fifth_octic_upper_data β z hx hy hX hzroot
  obtain ⟨hr₁,hi₁,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  have hslow : α=(22-3*Real.sqrt 22)/4 ∧ b=(92-9*Real.sqrt 22)/32 ∧ e=fifthOcticRemainder z ∧
      0 ≤ (3*(e.re/z.re)-e.im/z.im)/2 := by
    rcases hcases with hs|⟨ha,hb,hAlo,hAhi,hBlo,hBhi⟩
    · exact hs
    · exfalso
      subst α
      subst b
      by_cases hvy : z.im ≤ w.im
      · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ _ b₀ _
          (E₀.re/w.re) (e.re/z.re) (3/5) (39/200) 0 hR hwpos hy.le hxz hvy hWedge
          (by linarith) hα7p hA₀hi hAlo (by dsimp [α₀,b₀] at *; linarith only [hαp,hα₀up,hb₀lo,hbfast]) hR₀ hR₁
      · exact fast_graph_northeast_impossible α₀ _ b₀ _ (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
          (3/5) (5/8) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
          hR hI.le hwX hα₀.le (by linarith) (by linarith) hB₀hi (by linarith) (by dsimp [α₀,b₀] at *; linarith only [hαp,hα₀up,hb₀lo,hbfast]) hI₀ hR₁ hI₁
  rcases hslow with ⟨rfl,rfl,rfl,hC₁⟩
  have himorder : w.im ≤ z.im := by
    by_contra hn
    exact inverse_graph_southeast_impossible α₀ _ b₀ _ (E₀.re/w.re) ((fifthOcticRemainder z).re/z.re)
      (E₀.im/w.im) ((fifthOcticRemainder z).im/z.im) (39/100) β.re β.im w.re w.im z.re z.im
      (by linarith) hαm7 hwpos hy hxz (le_of_not_ge hn) hR hI.le hC₀ hC₁ hgap hR₀ hI₀ hR₁ hI₁
  exact ⟨z,hzroot,hxz,himorder,hgraph⟩
