-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fourth_septic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T16:01:05.921898+00:00
-- url     : https://prove2.me/submissions/44707485-5883-4864-8937-f2f09a7fc9b2

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
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







theorem sexticUpperBranch_sq (a b c : ℝ) (z : ℂ) :
    (sexticUpperBranch a b c z)^2 = sexticRadicand a b c z := by
  rw [sexticUpperBranch,mul_pow]
  have hs : (Complex.sqrt (-sexticRadicand a b c z))^2 = -sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  rw [hs,Complex.I_sq]
  ring

theorem sexticUpperBranch_im_pos (a b c : ℝ) (z : ℂ)
    (havoid : (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0) :
    0 < (sexticUpperBranch a b c z).im := by
  simp only [sexticUpperBranch,Complex.mul_im,Complex.I_re,Complex.I_im,
    one_mul,zero_mul,zero_add]
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases havoid with hi | hr
  · have hn := Complex.abs_re_lt_norm.mpr (show (-sexticRadicand a b c z).im ≠ 0 by simpa using hi)
    have ha := neg_abs_le (-sexticRadicand a b c z).re
    linarith
  · simp only [Complex.neg_re]
    have hn := norm_nonneg (-sexticRadicand a b c z)
    linarith

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
-- Source module: SexticBoundary


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sexticRadicand_im_identity (a b c : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (sexticRadicand a b c z).im*(z.re^2+z.im^2) =
      z.im*((2*z.re+a)*(z.re^2+z.im^2)-c) := by
  have hd : z.re^2+z.im^2 ≠ 0 := by
    simpa [Complex.normSq_apply,pow_two] using ne_of_gt (Complex.normSq_pos.mpr hz)
  simp only [sexticRadicand,pow_two,Complex.add_im,Complex.mul_im,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.div_im]
  simp only [Complex.normSq_apply]
  field_simp
  ring

theorem sexticRadicand_real (a b c x : ℝ) :
    sexticRadicand a b c (x : ℂ) = ((x^2+a*x+b+c/x : ℝ) : ℂ) := by
  simp [sexticRadicand]

theorem fourth_sextic_real_exterior (x : ℝ) (hx : x ≤ -1/4 ∨ 3/2 ≤ x) :
    0 < x^2+(-11/5)*x+121/120+(1331/7560)/x := by
  rcases hx with hl | hr
  · have hx0 : x < 0 := by linarith
    have h3 : 0 ≤ (-1/4-x)^3 := pow_nonneg (by linarith) 3
    have h2 := sq_nonneg (x+1/4)
    have he : (x^2+(-11/5)*x+121/120+(1331/7560)/x)*x =
      x^3+(-11/5)*x^2+(121/120)*x+1331/7560 := by field_simp [ne_of_lt hx0] <;> ring
    nlinarith
  · have hx0 : 0 < x := by linarith
    have h3 : 0 ≤ (x-3/2)^3 := pow_nonneg (by linarith) 3
    have h2 := sq_nonneg (x-3/2)
    have he : (x^2+(-11/5)*x+121/120+(1331/7560)/x)*x =
      x^3+(-11/5)*x^2+(121/120)*x+1331/7560 := by field_simp [ne_of_gt hx0] <;> ring
    nlinarith



theorem sexticRadicand_slit_exterior (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (z : ℂ) (hz : z.re ≤ -1/4 ∨ 3/2 ≤ z.re) :
    sexticRadicand a b c z ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; rcases hz with h|h <;> norm_num at h
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he,sexticRadicand_real,Complex.ofReal_re]
    exact hreal _ hz
  · right
    have hid := sexticRadicand_im_identity a b c z hz0
    intro hzero
    rw [hzero,zero_mul] at hid
    have hfactor : (2*z.re+a)*(z.re^2+z.im^2)-c=0 :=
      (mul_eq_zero.mp hid.symm).resolve_left hi
    have hd : 0 < z.re^2+z.im^2 := by positivity
    rcases hz with hl|hr
    · have hf : 2*z.re+a < 0 := by linarith
      have hp := mul_neg_of_neg_of_pos hf hd
      linarith
    · have hf : 4/5 ≤ 2*z.re+a := by linarith
      have hd' : 9/4 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
      have hp := mul_le_mul hf hd' (by norm_num : (0:ℝ) ≤ 9/4) (by linarith : 0 ≤ 2*z.re+a)
      nlinarith

end DerivativeChainPrivate

end


section
-- Source module: SexticExtension


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sqrt_im_sign (w : ℂ) (hw : w.im ≠ 0) :
    0 < (Complex.sqrt w).re ∧ (Complex.sqrt w).im * w.im > 0 := by
  have hs : (Complex.sqrt w)^2 = w := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hr : 0 < (Complex.sqrt w).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    apply Real.sqrt_pos.mpr
    have hn := Complex.abs_re_lt_norm.mpr hw
    have ha := neg_abs_le w.re
    linarith
  have hi := congrArg Complex.im hs
  simp only [pow_two,Complex.mul_im] at hi
  have hsi : (Complex.sqrt w).im ≠ 0 := by intro he; simp [he] at hi; exact hw hi.symm
  have hp := mul_pos hr (sq_pos_of_ne_zero hsi)
  constructor
  · exact hr
  · have he := congrArg (fun x : ℝ => (Complex.sqrt w).im*x) hi
    nlinarith only [he,hp]

theorem sexticUpperBranch_eq_sqrt_of_im_pos (a b c : ℝ) (z : ℂ)
    (hi : 0 < (sexticRadicand a b c z).im) :
    sexticUpperBranch a b c z = Complex.sqrt (sexticRadicand a b c z) := by
  have hF := sexticUpperBranch_im_pos a b c z (Or.inl (ne_of_gt hi))
  have hS := (sqrt_im_sign _ (ne_of_gt hi)).2
  have hSpos : 0 < (Complex.sqrt (sexticRadicand a b c z)).im := by nlinarith
  have hs : (Complex.sqrt (sexticRadicand a b c z))^2 = sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ((sexticUpperBranch_sq a b c z).trans hs.symm) with h|h
  · exact h
  · have hh := congrArg Complex.im h
    simp only [Complex.neg_im] at hh
    linarith



theorem sexticRadicand_im_right (a b c : ℝ) (ha : -11/5 ≤ a) (hc : c ≤ 1)
    (z : ℂ) (hx : 3/2 ≤ z.re) (hy : 0 < z.im) :
    0 < (sexticRadicand a b c z).im := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hy
  have hd : 0 < z.re^2+z.im^2 := by positivity
  have hf : 4/5 ≤ 2*z.re+a := by linarith
  have hd' : 9/4 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hp := mul_le_mul hf hd' (by norm_num : (0:ℝ) ≤ 9/4) (by linarith : 0 ≤ 2*z.re+a)
  have hfpos : 0 < (2*z.re+a)*(z.re^2+z.im^2)-c := by nlinarith
  have hi := sexticRadicand_im_identity a b c z hz0
  have hm := mul_pos hy hfpos
  nlinarith



end DerivativeChainPrivate

end


section
-- Source module: SexticSupport


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set



theorem sexticExteriorExtension_continuous (a b c σ : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf0 : ∀ x, f x ≠ 0)
    (hslit : ∀ z : ℂ, sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) ∈ Complex.slitPlane) :
    Continuous (sexticExteriorExtension a b c σ f) := by
  have hw : Continuous (fun z : ℂ => ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) := by fun_prop
  have hw0 : ∀ z : ℂ, ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) ≠ 0 := by
    intro z h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_self,add_zero,Complex.zero_re] at hr
    exact hf0 _ hr
  have hH : Continuous (fun z : ℂ => sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) := by
    unfold sexticRadicand
    fun_prop
  have hs : Continuous (fun z : ℂ => Complex.sqrt (sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [Function.comp_def] using
      ContinuousAt.comp (f := fun w : ℂ => sexticRadicand a b c ((f w.re:ℂ)+Complex.I*(w.im:ℂ)))
        (Complex.differentiableAt_sqrt (hslit z)).continuousAt (hH.continuousAt (x := z))
  unfold sexticExteriorExtension
  fun_prop





end DerivativeChainPrivate

end


section
-- Source module: CauchyBoundary


set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
namespace DerivativeChainPrivate

theorem borelTransform_vertical_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (B T : ℝ) (hT : B < T) (hμ : ∀ᵐ t ∂μ, t ≤ B) :
    Tendsto (fun ε : ℝ => TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝 0) (𝓝 (TeschlQM.Herglotz.borelTransform μ (T:ℂ))) := by
  unfold TeschlQM.Herglotz.borelTransform
  have hc : ContinuousAt (fun ε : ℝ => ∫ t : ℝ, ((t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I))⁻¹ ∂μ) 0 := by
    apply continuousAt_of_dominated (bound := fun _ => (T-B)⁻¹)
    · exact Eventually.of_forall (fun ε => ((Complex.measurable_ofReal.sub_const _).inv).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro ε
      filter_upwards [hμ] with t ht
      rw [norm_inv]
      apply inv_anti₀ (sub_pos.mpr hT)
      calc
        T-B ≤ T-t := by linarith
        _ ≤ |t-T| := by rw [abs_of_neg (by linarith : t-T < 0)]; ring_nf; rfl
        _ = |((t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I)).re| := by simp
        _ ≤ ‖(t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I)‖ := Complex.abs_re_le_norm _
    · exact integrable_const _
    · filter_upwards [hμ] with t ht
      apply ContinuousAt.inv₀ (by fun_prop)
      simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_ne_zero]
      exact_mod_cast (show t ≠ T by linarith)
  simpa using hc.tendsto

theorem sextic_measure_real_value (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ z : ℂ, 0 < z.im → sexticShift a b c z = TeschlQM.Herglotz.borelTransform μ z)
    (T : ℝ) (hT : 3/2 < T) :
    TeschlQM.Herglotz.borelTransform μ (T:ℂ) =
      ((Real.sqrt (T^2+a*T+b+c/T)-T-a/2 : ℝ):ℂ) := by
  let f : ℝ → ℝ := fun x => max (3/2) x
  let E := sexticExteriorExtension a b c 1 f
  have hf : ∀ x, 3/2 ≤ f x := fun x => le_max_left _ _
  have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
  have hE : Continuous E := sexticExteriorExtension_continuous a b c 1 f
    (by dsimp [f]; fun_prop) hf0 (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
      (Or.inr (by simpa using hf z.re)))
  have heq : ∀ ε : ℝ, 0 < ε → E ((T:ℂ)+(ε:ℂ)*Complex.I) =
      TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I) := by
    intro ε hε
    have hz : 0 < ((T:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
    rw [← hμ _ hz]
    dsimp only [E,sexticExteriorExtension,sexticShift]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      zero_mul,zero_add,sub_zero,add_zero,Complex.ofReal_one,one_mul]
    rw [show f T = T by exact max_eq_right hT.le]
    rw [sexticUpperBranch_eq_sqrt_of_im_pos a b c _
      (sexticRadicand_im_right a b c ha hc1 _ (by simpa using hT.le) hz)]
    congr 2 <;> ring
  have hv : E (T:ℂ) = ((Real.sqrt (T^2+a*T+b+c/T)-T-a/2 : ℝ):ℂ) := by
    dsimp only [E,sexticExteriorExtension]
    simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,mul_zero,add_zero,
      Complex.ofReal_one,one_mul]
    rw [show f T = T by exact max_eq_right hT.le,sexticRadicand_real]
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (hreal T (Or.inr hT.le)).le)]
    simp only [Complex.ofReal_re]
    push_cast
    rfl
  have hlim : Tendsto (fun ε : ℝ => E ((T:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>]0) (𝓝 (E (T:ℂ))) := by
    have ht : Tendsto (fun ε : ℝ => ((T:ℂ)+(ε:ℂ)*Complex.I)) (𝓝 0) (𝓝 (T:ℂ)) := by
      simpa using (show Continuous (fun ε : ℝ => ((T:ℂ)+(ε:ℂ)*Complex.I)) by fun_prop).tendsto 0
    exact (hE.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds
  have hlim' := (borelTransform_vertical_limit μ (3/2) T hT (hsupp.mono fun t ht => ht.2)).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hevent : (fun ε : ℝ => E ((T:ℂ)+(ε:ℂ)*Complex.I)) =ᶠ[𝓝[>]0]
      (fun ε : ℝ => TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using heq ε hε
  exact (tendsto_nhds_unique hlim' (hlim.congr' hevent)).trans hv

end DerivativeChainPrivate

namespace DerivativeChainPrivate
open MeasureTheory

theorem real_cauchy_integral_of_borel_value (μ : Measure ℝ) (T V : ℝ)
    (hV : TeschlQM.Herglotz.borelTransform μ (T:ℂ) = (V:ℂ)) :
    (∫ t : ℝ, 1/(T-t) ∂μ) = -V := by
  have hi : TeschlQM.Herglotz.borelTransform μ (T:ℂ) =
      -((∫ t : ℝ, 1/(T-t) ∂μ : ℝ):ℂ) := by
    unfold TeschlQM.Herglotz.borelTransform
    rw [← integral_complex_ofReal,← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      push_cast
      rw [one_div,← inv_neg]
      congr 1
      ring)
  rw [hV] at hi
  have hr := congrArg Complex.re hi
  simp only [Complex.ofReal_re,Complex.neg_re] at hr
  linarith

end DerivativeChainPrivate

end


section
-- Source module: MeasureKernels


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sextic_kernel_bounds (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    let D := (X-t)^2+2*(X+t)*Y+Y^2
    0 < D ∧ 0 ≤ (X+Y-t)/D ∧ 0 ≤ (X+Y+t)/D ∧
      0 ≤ (2*(X+Y)-t)/D ∧ (X+Y-t)/D ≤ 1/(T-t) := by
  have hXt : 0 < X-t := by linarith
  have hTt : 0 < T-t := by linarith
  have hXp : 0 < X+t := by linarith
  have hX3t : 0 < X+3*t := by linarith
  have hD : 0 < (X-t)^2+2*(X+t)*Y+Y^2 := by positivity
  refine ⟨hD,div_nonneg (by linarith) hD.le,div_nonneg (by linarith) hD.le,
    div_nonneg (by linarith) hD.le,?_⟩
  apply le_trans (b := 1/(X-t))
  · apply (div_le_div_iff₀ hD hXt).mpr
    have hp := mul_nonneg hX3t.le hY
    nlinarith only [hp,sq_nonneg Y]
  · exact one_div_le_one_div_of_le hTt (by linarith)




theorem sextic_kernel_inverse_bound (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    1/((X-t)^2+2*(X+t)*Y+Y^2) ≤ (1/(T-t))/(T-3/2) := by
  have hXt : 0 < X-t := by linarith
  have hTt : 0 < T-t := by linarith
  have hTb : 0 < T-3/2 := by linarith
  have hXp : 0 < X+t := by linarith
  have hD : 0 < (X-t)^2+2*(X+t)*Y+Y^2 := by positivity
  rw [div_div]
  apply (div_le_div_iff₀ hD (mul_pos hTt hTb)).mpr
  have hp := mul_nonneg hXp.le hY
  have htprod := mul_nonneg (show 0 ≤ 3/2-t by linarith) hTt.le
  have hxprod := mul_nonneg (show 0 ≤ X-T by linarith) (show 0 ≤ X+T-2*t by linarith)
  nlinarith only [hp,htprod,hxprod,sq_nonneg Y]

theorem sextic_kernel_B_bound (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    (X+Y+t)/((X-t)^2+2*(X+t)*Y+Y^2) ≤ (1+3/(T-3/2))*(1/(T-t)) := by
  obtain ⟨hD,_,_,_,hA⟩ := sextic_kernel_bounds X Y t T hT hX hY htl htu
  have hInv := sextic_kernel_inverse_bound X Y t T hT hX hY htl htu
  have ht : 2*t/((X-t)^2+2*(X+t)*Y+Y^2) ≤ 3/((X-t)^2+2*(X+t)*Y+Y^2) := by
    apply div_le_div_of_nonneg_right (by linarith) hD.le
  calc
    _ = (X+Y-t)/((X-t)^2+2*(X+t)*Y+Y^2)+2*t/((X-t)^2+2*(X+t)*Y+Y^2) := by ring
    _ ≤ 1/(T-t)+3*((1/(T-t))/(T-3/2)) := by
      apply add_le_add hA
      apply ht.trans
      convert mul_le_mul_of_nonneg_left hInv (by norm_num : (0:ℝ) ≤ 3) using 1 <;> ring
    _ = _ := by ring

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

theorem cauchy_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hx : 5/2 ≤ z.re^2) :
    Integrable (fun t : ℝ => (z^2-(t:ℂ))⁻¹) μ := by
  apply Integrable.of_bound ((measurable_const.sub Complex.measurable_ofReal).inv).aestronglyMeasurable
    (z.re^2-3/2)⁻¹
  filter_upwards [hsupp] with t ht
  exact (cauchy_root_kernel_bound z hx t ht).2

theorem cauchy_root_kernel_parts (z : ℂ) (hxpos : 0 < z.re)
    (hx : 5/2 ≤ z.re^2) (t : ℝ) (ht : t ∈ Icc (-1/4:ℝ) (3/2)) :
    let D := (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4
    (z/(z^2-(t:ℂ))).re = z.re*((z.re^2+z.im^2-t)/D) ∧
    (z/(z^2-(t:ℂ))).im = -z.im*((z.re^2+z.im^2+t)/D) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hxpos
  have hpole := (cauchy_root_kernel_bound z hx t ht).1
  obtain ⟨hr,hi,_,hd⟩ := rational_inverse_parts (z/(z^2-(t:ℂ))) z 0 0 1 t hz hpole
    (by simp; field_simp)
  simp only [Complex.ofReal_zero,Complex.ofReal_one,zero_mul,sub_zero,zero_add,one_mul,zero_sub] at hr hi
  have hd' : ‖z^2-(t:ℂ)‖^2 = (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 := by
    rw [hd]; ring
  rw [hd'] at hr hi
  refine ⟨hr,?_⟩
  simpa only [mul_neg,neg_mul] using hi

end DerivativeChainPrivate

end


section
-- Source module: CauchyRootBounds


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_real_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) (T : ℝ) (hT : 3/2 < T) :
    Integrable (fun t : ℝ => 1/(T-t)) μ := by
  have hm : Measurable (fun t : ℝ => 1/(T-t)) := measurable_const.div (measurable_const.sub measurable_id)
  apply Integrable.of_bound hm.aestronglyMeasurable (1/(T-3/2))
  filter_upwards [hsupp] with t ht
  have hp : 0 < T-t := by linarith [ht.2]
  rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hp)]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [ht.2])

theorem cauchy_root_corrections (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hxpos : 0 < z.re) (hypos : 0 < z.im)
    (T : ℝ) (hT : 5/2 ≤ T) (hx : T ≤ z.re^2) :
    let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
    0 ≤ E.re/z.re ∧ E.re/z.re ≤ ∫ t : ℝ, 1/(T-t) ∂μ ∧
      0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 := by
  let f : ℝ → ℂ := fun t => z/(z^2-(t:ℂ))
  have hf : Integrable f μ := by
    simpa [f,div_eq_mul_inv] using (cauchy_kernel_integrable μ hsupp z (hT.trans hx)).const_mul z
  have hE : z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) = ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    simp only [f,div_eq_mul_inv]
  dsimp only
  rw [hE]
  have hAre : Integrable (fun t => (f t).re/z.re) μ := hf.re.div_const _
  have hBim : Integrable (fun t => (f t).im/z.im) μ := hf.im.div_const _
  have hA : (∫ t, f t ∂μ).re/z.re = ∫ t, (f t).re/z.re ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.re) (integral_re hf).symm
  have hB : (∫ t, f t ∂μ).im/z.im = ∫ t, (f t).im/z.im ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.im) (integral_im hf).symm
  rw [hA,hB]
  have hparts : ∀ᵐ t ∂μ,
      0 ≤ (f t).re/z.re ∧ (f t).re/z.re ≤ 1/(T-t) ∧
      0 ≤ (3*((f t).re/z.re)-(f t).im/z.im)/2 := by
    filter_upwards [hsupp] with t ht
    obtain ⟨hr,hi⟩ := cauchy_root_kernel_parts z hxpos (hT.trans hx) t ht
    obtain ⟨hd,hAp,_,hCp,hAub⟩ := sextic_kernel_bounds (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hD : (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 =
        (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+(z.im^2)^2 := by ring
    dsimp only [f]
    rw [hr,hi]
    simp only [mul_div_cancel_left₀ _ hxpos.ne',neg_mul,neg_div,mul_div_cancel_left₀ _ hypos.ne']
    rw [hD]
    refine ⟨hAp,hAub,?_⟩
    convert hCp using 1 <;> ring
  refine ⟨integral_nonneg_of_ae (hparts.mono fun t ht => ht.1),
    integral_mono_ae hAre (cauchy_real_kernel_integrable μ hsupp T (by linarith))
      (hparts.mono fun t ht => ht.2.1),?_⟩
  have hpos := integral_nonneg_of_ae (hparts.mono fun t ht => ht.2.2)
  simpa only [integral_div,integral_sub (hAre.const_mul 3) hBim,integral_const_mul] using hpos

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
-- Source module: FourthSexticScalars


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem fourth_sextic_numeric_gaps :
    let s := Real.sqrt 70
    let αm := (28-3*s)/55
    let αp := (28+3*s)/55
    let bm := (35-3*s)/50
    let bp := (35+3*s)/50
    let k := 3*s/55
    0 < k ∧ k < 1/2 ∧ 1/20 < αm ∧ αm < 1/10 ∧
      9/10 < αp ∧ bp < 5/4 ∧ 3/50 < 23/80-bm ∧ 0 < bm := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 70)
  have hp := Real.sqrt_nonneg 70
  dsimp only
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> nlinarith

end DerivativeChainPrivate

end


section
-- Source module: CauchyRootImag


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_root_imaginary_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hxpos : 0 < z.re) (hypos : 0 < z.im)
    (T : ℝ) (hT : 5/2 ≤ T) (hx : T ≤ z.re^2) :
    let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
    E.im/z.im ≤ 0 ∧ -(1+3/(T-3/2))*(∫ t : ℝ, 1/(T-t) ∂μ) ≤ E.im/z.im := by
  let f : ℝ → ℂ := fun t => z/(z^2-(t:ℂ))
  have hf : Integrable f μ := by
    simpa [f,div_eq_mul_inv] using (cauchy_kernel_integrable μ hsupp z (hT.trans hx)).const_mul z
  have hE : z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) = ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    simp only [f,div_eq_mul_inv]
  dsimp only
  rw [hE]
  have hBim : Integrable (fun t => (f t).im/z.im) μ := hf.im.div_const _
  have hB : (∫ t, f t ∂μ).im/z.im = ∫ t, (f t).im/z.im ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.im) (integral_im hf).symm
  rw [hB]
  have hparts : ∀ᵐ t ∂μ, (f t).im/z.im ≤ 0 ∧
      -(1+3/(T-3/2))*(1/(T-t)) ≤ (f t).im/z.im := by
    filter_upwards [hsupp] with t ht
    obtain ⟨_,hi⟩ := cauchy_root_kernel_parts z hxpos (hT.trans hx) t ht
    obtain ⟨_,_,hBp,_,_⟩ := sextic_kernel_bounds (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hBu := sextic_kernel_B_bound (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hD : (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 =
        (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+(z.im^2)^2 := by ring
    dsimp only [f]
    rw [hi]
    simp only [neg_mul,neg_div,mul_div_cancel_left₀ _ hypos.ne']
    rw [hD]
    constructor <;> linarith
  constructor
  · exact integral_nonpos_of_ae (hparts.mono fun t ht => ht.1)
  · have hb := integral_mono_ae ((cauchy_real_kernel_integrable μ hsupp T (by linarith)).const_mul
        (-(1+3/(T-3/2)))) hBim (hparts.mono fun t ht => ht.2)
    simpa only [integral_const_mul] using hb

end DerivativeChainPrivate

end


section
-- Source module: FourthSexticCorrections


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem fourth_sextic_bound_at_ten_thirds :
    (10/3:ℝ)+(-11/5)/2-Real.sqrt ((10/3)^2+(-11/5)*(10/3)+121/120+(1331/7560)/(10/3)) < 17/500 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (10/3)^2+(-11/5)*(10/3)+121/120+(1331/7560)/(10/3))
  have hp := Real.sqrt_nonneg ((10/3:ℝ)^2+(-11/5)*(10/3)+121/120+(1331/7560)/(10/3))
  norm_num at hs hp ⊢
  nlinarith

theorem fourth_sextic_correction_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 10/3 ≤ z.re^2) :
    let E := ((3*Real.sqrt 70/55:ℝ):ℂ)*(z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ))
    0 ≤ E.re/z.re ∧ E.re/z.re ≤ 391/25000 ∧ E.im/z.im ≤ 0 ∧
      0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 ∧ (3*(E.re/z.re)-E.im/z.im)/2 ≤ 9/200 := by
  let k := 3*Real.sqrt 70/55
  let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
  let M := ∫ t : ℝ, 1/((10/3)-t) ∂μ
  obtain ⟨hA0,hAM,hC⟩ := cauchy_root_corrections μ hsupp z hx hy (10/3) (by norm_num) hX
  obtain ⟨hB0,hBM⟩ := cauchy_root_imaginary_bounds μ hsupp z hx hy (10/3) (by norm_num) hX
  change 0 ≤ E.re/z.re at hA0
  change E.re/z.re ≤ M at hAM
  change 0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 at hC
  change E.im/z.im ≤ 0 at hB0
  change -(1+3/((10/3:ℝ)-3/2))*M ≤ E.im/z.im at hBM
  norm_num at hBM
  have hk : 0 < k := by dsimp [k]; positivity
  have hku : k < 23/50 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 70)
    have hp := Real.sqrt_nonneg 70
    dsimp only [k]
    nlinarith
  have hMlt : M < 17/500 := by
    have hb := sextic_measure_real_value (-11/5) (121/120) (1331/7560)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fourth_sextic_real_exterior μ hsupp hμ (10/3) (by norm_num)
    have ht := real_cauchy_integral_of_borel_value μ (10/3) _ hb
    have he : M = (10/3:ℝ)+(-11/5)/2-
        Real.sqrt ((10/3)^2+(-11/5)*(10/3)+121/120+(1331/7560)/(10/3)) := by
      dsimp only [M]; linarith only [ht]
    rw [he]
    exact fourth_sextic_bound_at_ten_thirds
  have hM0 : 0 ≤ M := hA0.trans hAM
  have hkM : k*M ≤ 391/25000 := by
    have hp := mul_le_mul hku.le hMlt.le hM0 (by norm_num : (0:ℝ) ≤ 23/50)
    norm_num at hp
    exact hp
  have hAr : ((k:ℂ)*E).re/z.re = k*(E.re/z.re) := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; ring
  have hBi : ((k:ℂ)*E).im/z.im = k*(E.im/z.im) := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; ring
  change 0 ≤ ((k:ℂ)*E).re/z.re ∧ _
  rw [hAr,hBi]
  have hA := mul_le_mul_of_nonneg_left hAM hk.le
  have hB := mul_le_mul_of_nonneg_left hBM hk.le
  have hCC := mul_nonneg hk.le hC
  refine ⟨mul_nonneg hk.le hA0,by linarith,mul_nonpos_of_nonneg_of_nonpos hk.le hB0,?_,?_⟩
  · nlinarith only [hCC]
  · nlinarith only [hA,hB,hkM]

end DerivativeChainPrivate

end


section
-- Source module: SepticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators













theorem septic_sqrt_remainder_identity (u : ℂ) :
    septicSqrtRadicand u-(septicSqrtPoly u)^2 = u^8*septicSqrtResidual u := by
  norm_num [septicSqrtRadicand,septicSqrtPoly,septicSqrtResidual,
    septicSqrtCoeffs,septicResidualCoeffs,Fin.sum_univ_succ]
  ring

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
-- Source module: SepticInverseAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem septic_sqrt_exact_remainder (u : ℂ) (hu : ‖u‖ ≤ 4/9) :
    Complex.sqrt (septicSqrtRadicand u) = septicSqrtPoly u+
      u^8*septicSqrtResidual u/(Complex.sqrt (septicSqrtRadicand u)+septicSqrtPoly u) := by
  have hd := (septic_sqrt_denominator_bound u hu).1
  have hs : (Complex.sqrt (septicSqrtRadicand u))^2 = septicSqrtRadicand u :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have he : (Complex.sqrt (septicSqrtRadicand u)-septicSqrtPoly u)*
      (Complex.sqrt (septicSqrtRadicand u)+septicSqrtPoly u) = u^8*septicSqrtResidual u := by
    calc
      _ = (Complex.sqrt (septicSqrtRadicand u))^2-(septicSqrtPoly u)^2 := by ring
      _ = _ := by rw [hs,septic_sqrt_remainder_identity]
  have hh := (eq_div_iff hd).mpr he
  linear_combination hh

theorem septic_polynomial_error_identity (w : ℂ) :
    w^3*((septicLeadingError:ℂ)*w+septicPolynomialError w) =
      (11/120)*w^4-((3*Real.sqrt 3/55:ℝ):ℂ)*
        ((1-(11/6)*w^2)*septicSqrtPoly (w^2)-1+(77/36)*w^2) := by
  norm_num [septicLeadingError,septicPolynomialError,septicSqrtPoly,septicErrorCoeffs,
    septicSqrtCoeffs,Fin.sum_univ_succ]
  push_cast
  ring

theorem septic_tail_identity (w : ℂ) (hw : ‖w^2‖ ≤ 4/9) :
    w^3*septicTail w = -((3*Real.sqrt 3/55:ℝ):ℂ)*(1-(11/6)*w^2)*
      (Complex.sqrt (septicSqrtRadicand (w^2))-septicSqrtPoly (w^2)) := by
  have hs := septic_sqrt_exact_remainder (w^2) hw
  have he : Complex.sqrt (septicSqrtRadicand (w^2))-septicSqrtPoly (w^2) =
      (w^2)^8*septicSqrtResidual (w^2)/(Complex.sqrt (septicSqrtRadicand (w^2))+septicSqrtPoly (w^2)) := by
    linear_combination hs
  rw [he]
  dsimp only [septicTail]
  ring

theorem septic_remainder_exact (z : ℂ) (hz : z ≠ 0) (hn : ‖z⁻¹‖^2 ≤ 3/10) :
    septicRemainder z = (11/120)/z-((3*Real.sqrt 3/55:ℝ):ℂ)*z^3*
      ((1-(11/6)*(z⁻¹)^2)*Complex.sqrt (septicSqrtRadicand ((z⁻¹)^2))-1+(77/36)*(z⁻¹)^2) := by
  have hw : ‖(z⁻¹)^2‖ ≤ 4/9 := by rw [norm_pow]; linarith
  have hP := septic_polynomial_error_identity z⁻¹
  have hT := septic_tail_identity z⁻¹ hw
  have hR : (z⁻¹)^3*septicRemainder z = (11/120)*(z⁻¹)^4-
      ((3*Real.sqrt 3/55:ℝ):ℂ)*((1-(11/6)*(z⁻¹)^2)*
        Complex.sqrt (septicSqrtRadicand ((z⁻¹)^2))-1+(77/36)*(z⁻¹)^2) := by
    dsimp only [septicRemainder,septicError]
    linear_combination hP+hT
  apply mul_left_cancel₀ (pow_ne_zero 3 (inv_ne_zero hz))
  rw [hR]
  field_simp <;> ring

theorem septic_inverse_exact (z : ℂ) (hz : z ≠ 0) (hn : ‖z⁻¹‖^2 ≤ 3/10) :
    (((7-3*Real.sqrt 3)/55:ℝ):ℂ)*z^2-((7*(3-Real.sqrt 3)/60:ℝ):ℂ)+septicRemainder z/z =
      (7/55)*z^2-7/20+(11/120)/z^2-((3*Real.sqrt 3/55:ℝ):ℂ)*(z^2-11/6)*
        Complex.sqrt (septicSqrtRadicand ((z⁻¹)^2)) := by
  rw [septic_remainder_exact z hz hn]
  push_cast
  field_simp <;> ring

end DerivativeChainPrivate

end


section
-- Source module: FourthSepticGraphs


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_septic_upper_graphs (β z : ℂ) (hx : 0 < z.re) (hX : 10/3 ≤ z.re^2)
    (hroot : (275/2)*β^2*z-35*β*z^4+(385/4)*β*z^2-(605/24)*β+
      z^7-7*z^5+(77/6)*z^3-(121/24)*z=0) :
    β/z = (((7-3*Real.sqrt 3)/55:ℝ):ℂ)*z^2-((7*(3-Real.sqrt 3)/60:ℝ):ℂ)+septicRemainder z/z ∨
    β/z = (((7+3*Real.sqrt 3)/55:ℝ):ℂ)*z^2-((7*(3+Real.sqrt 3)/60:ℝ):ℂ)+
      ((11/60)/z-septicRemainder z)/z := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hnorm : 10/3 ≤ ‖z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hn : ‖z⁻¹‖^2 ≤ 3/10 := by
    rw [norm_inv,inv_pow]
    apply (inv_le_comm₀ (by positivity : 0 < ‖z‖^2) (by norm_num)).mpr
    norm_num
    exact hnorm
  let S := Complex.sqrt (septicSqrtRadicand ((z⁻¹)^2))
  let s : ℂ := (Real.sqrt 3:ℂ)
  have hs : s^2 = 3 := by
    dsimp [s]
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hS : S^2 = septicSqrtRadicand ((z⁻¹)^2) := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hd : (275*β*z-35*z^4+(385/4)*z^2-605/24)^2 =
      (25/576)*(6*z^2-11)^2*(432*z^4-264*z^2+121) := by
    linear_combination 550*z*hroot
  have hsquare : (15*s*z^2*(z^2-11/6)*S)^2 =
      (25/576)*(6*z^2-11)^2*(432*z^4-264*z^2+121) := by
    calc
      _ = 225*s^2*z^4*(z^2-11/6)^2*S^2 := by ring
      _ = _ := by rw [hs,hS]; unfold septicSqrtRadicand; field_simp; ring
  have hsplit := (sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  have hbase : β/z = (7/55)*z^2-7/20+(11/120)/z^2-(3*s/55)*(z^2-11/6)*S ∨
      β/z = (7/55)*z^2-7/20+(11/120)/z^2+(3*s/55)*(z^2-11/6)*S := by
    rcases hsplit with hp|hm
    · right
      have hv : β/z = (35*z^4-(385/4)*z^2+605/24+15*s*z^2*(z^2-11/6)*S)/(275*z^2) := by
        apply (div_eq_div_iff hz (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))).mpr
        linear_combination z*hp
      rw [hv]
      field_simp
      ring
    · left
      have hv : β/z = (35*z^4-(385/4)*z^2+605/24-15*s*z^2*(z^2-11/6)*S)/(275*z^2) := by
        apply (div_eq_div_iff hz (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))).mpr
        linear_combination z*hm
      rw [hv]
      field_simp
      ring
  have hminus := septic_inverse_exact z hz hn
  change _ = (7/55)*z^2-7/20+(11/120)/z^2-((3*Real.sqrt 3/55:ℝ):ℂ)*(z^2-11/6)*S at hminus
  have hplus : (((7+3*Real.sqrt 3)/55:ℝ):ℂ)*z^2-((7*(3+Real.sqrt 3)/60:ℝ):ℂ)+
      ((11/60)/z-septicRemainder z)/z =
      (7/55)*z^2-7/20+(11/120)/z^2+(3*s/55)*(z^2-11/6)*S := by
    calc
      _ = (14/55)*z^2-7/10+(11/60)/z^2-
          ((((7-3*Real.sqrt 3)/55:ℝ):ℂ)*z^2-((7*(3-Real.sqrt 3)/60:ℝ):ℂ)+septicRemainder z/z) := by
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
-- Source module: FourthSepticUpperData


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_septic_upper_data (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 10/3 ≤ z.re^2)
    (hroot : (275/2)*β^2*z-35*β*z^4+(385/4)*β*z^2-(605/24)*β+
      z^7-7*z^5+(77/6)*z^3-(121/24)*z=0) :
    ∃ α b : ℝ, ∃ e : ℂ, 3/100 < α ∧ β/z = (α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((α = (7-3*Real.sqrt 3)/55 ∧ b = 7*(3-Real.sqrt 3)/60 ∧ e = septicRemainder z ∧
          0 ≤ (3*(e.re/z.re)-e.im/z.im)/2) ∨
       (α = (7+3*Real.sqrt 3)/55 ∧ b = 7*(3+Real.sqrt 3)/60 ∧
          0 ≤ e.re/z.re ∧ e.re/z.re ≤ 11/200 ∧ -(11/200) ≤ e.im/z.im ∧ e.im/z.im ≤ 0)) := by
  obtain ⟨hAp,hAu,hBl,hBn,hCp,hCu,hAr,hBr⟩ := septic_remainder_coordinate_bounds z hx hy hX
  obtain ⟨hαm,hαm6,hgap,hW,hαp,_,_,_,_⟩ := fourth_septic_scalar_gaps
  rcases fourth_septic_upper_graphs β z hx hX hroot with hm|hp
  · refine ⟨(7-3*Real.sqrt 3)/55,7*(3-Real.sqrt 3)/60,septicRemainder z,hαm,hm,?_,
      Or.inl ⟨rfl,rfl,rfl,hCp.le⟩⟩
    apply cubic_graph_positive_phase_of_corrections β z (septicRemainder z) _ _ (27/2000)
      hx hy (by linarith) (by norm_num) (by linarith) hAu _ hm
    linarith only [hBl]
  · let E := (11/60:ℂ)/z-septicRemainder z
    let U := z.re^2+z.im^2
    have hU : 10/3 ≤ U := by dsimp [U]; nlinarith [sq_nonneg z.im]
    have hUp : 0 < U := by linarith
    have hUn : Complex.normSq z = U := by simp [U,Complex.normSq_apply,pow_two]
    have hArat : ((11/60:ℂ)/z).re/z.re = (11/60:ℝ)/U := by
      rw [div_eq_mul_inv]
      simp only [Complex.mul_re,Complex.div_re,Complex.inv_re,Complex.inv_im,hUn]
      norm_num
      field_simp
    have hBrat : ((11/60:ℂ)/z).im/z.im = -(11/60:ℝ)/U := by
      rw [div_eq_mul_inv]
      simp only [Complex.mul_im,Complex.div_im,Complex.inv_re,Complex.inv_im,hUn]
      norm_num
      field_simp
    have hAe : E.re/z.re = (11/60:ℝ)/U-(septicRemainder z).re/z.re := by
      simp only [E,Complex.sub_re,sub_div,hArat]
    have hBe : E.im/z.im = -(11/60:ℝ)/U-(septicRemainder z).im/z.im := by
      simp only [E,Complex.sub_im,sub_div,hBrat]
    have hcompare : (9/200:ℝ)/U ≤ (11/60:ℝ)/U := div_le_div_of_nonneg_right (by norm_num) hUp.le
    have hbound : (11/60:ℝ)/U ≤ 11/200 := by apply (div_le_iff₀ hUp).mpr; linarith
    change (septicRemainder z).re/z.re ≤ (9/200:ℝ)/U at hAr
    change -(9/200:ℝ)/U ≤ (septicRemainder z).im/z.im at hBr
    simp only [neg_div] at hBr hBe
    have hA0 : 0 ≤ E.re/z.re := by rw [hAe]; linarith
    have hA1 : E.re/z.re ≤ 11/200 := by rw [hAe]; linarith
    have hB0 : -(11/200) ≤ E.im/z.im := by rw [hBe]; linarith
    have hB1 : E.im/z.im ≤ 0 := by rw [hBe]; linarith
    refine ⟨(7+3*Real.sqrt 3)/55,7*(3+Real.sqrt 3)/60,E,by linarith,hp,?_,
      Or.inr ⟨rfl,rfl,hA0,hA1,hB0,hB1⟩⟩
    apply cubic_graph_positive_phase_of_corrections β z E _ _ (11/200) hx hy (by linarith)
      (by norm_num) (by linarith) hA1 _ hp
    linarith only [hB0]

end DerivativeChainPrivate

end


section
-- Source module: FourthSepticPhase


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_septic_real_root_parameter (β : ℂ) (x : ℝ) (hx : 0 < x)
    (hroot : (275/2)*β^2*(x:ℂ)-35*β*(x:ℂ)^4+(385/4)*β*(x:ℂ)^2-(605/24)*β+
      (x:ℂ)^7-7*(x:ℂ)^5+(77/6)*(x:ℂ)^3-(121/24)*(x:ℂ)=0) : β.im=0 := by
  let A := (275/2:ℝ)*x
  let B := -35*x^4+(385/4)*x^2-605/24
  let C := x^7-7*x^5+(77/6)*x^3-(121/24)*x
  have hquad : (A:ℂ)*β^2+(B:ℂ)*β+(C:ℂ)=0 := by
    dsimp [A,B,C]; push_cast; linear_combination hroot
  apply real_quadratic_root_im_of_nonzero_leading A B C (by dsimp [A]; positivity) _ β hquad
  have he : B^2-4*A*C = (25/576)*(6*x^2-11)^2*(432*x^4-264*x^2+121) := by dsimp [A,B,C]; ring
  have hp : 0 < 432*x^4-264*x^2+121 := by nlinarith [sq_nonneg (x^2-11/36)]
  rw [he]
  positivity

theorem fourth_septic_nonnegative_im (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 10/3 ≤ z.re^2)
    (hroot : (275/2)*β^2*z-35*β*z^4+(385/4)*β*z^2-(605/24)*β+
      z^7-7*z^5+(77/6)*z^3-(121/24)*z=0) :
    0 ≤ z.im ∧ (β.im=0 ↔ z.im=0) := by
  have hnonneg : 0 ≤ z.im := by
    by_contra hn
    have hy : z.im < 0 := lt_of_not_ge hn
    have hroot' : (275/2)*(starRingEnd ℂ β)^2*(starRingEnd ℂ z)-35*(starRingEnd ℂ β)*(starRingEnd ℂ z)^4+
        (385/4)*(starRingEnd ℂ β)*(starRingEnd ℂ z)^2-(605/24)*(starRingEnd ℂ β)+
        (starRingEnd ℂ z)^7-7*(starRingEnd ℂ z)^5+(77/6)*(starRingEnd ℂ z)^3-(121/24)*(starRingEnd ℂ z)=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fourth_septic_upper_data (starRingEnd ℂ β) (starRingEnd ℂ z)
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
    obtain ⟨α,b,e,_,_,hp,_⟩ := fourth_septic_upper_data β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    exact fourth_septic_real_root_parameter β z.re hx hroot

end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im) (hwpos : 0 < w.re) (hwim : 0 < w.im)
    (hwX : 10/3 ≤ w.re^2)
    (hwroot : (275/14)*β^2-20*β*w^3+(55/2)*β*w+w^6-5*w^4+(11/2)*w^2-121/168=0)
    (hwinv : β/w = (((28-3*Real.sqrt 70)/55:ℝ):ℂ)*w^2-(((35-3*Real.sqrt 70)/50:ℝ):ℂ)+
      ((3*Real.sqrt 70/55:ℝ):ℂ)*(∫ t : ℝ, (w^2-(t:ℂ))⁻¹ ∂μ)) :
    ∃ z : ℂ,
      (275/2)*β^2*z-35*β*z^4+(385/4)*β*z^2-(605/24)*β+
        z^7-7*z^5+(77/6)*z^3-(121/24)*z=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 4 < z.re^2 ∧
      β/z = (((7-3*Real.sqrt 3)/55:ℝ):ℂ)*z^2-((7*(3-Real.sqrt 3)/60:ℝ):ℂ)+septicRemainder z/z := by
  let α₀ := (28-3*Real.sqrt 70)/55
  let b₀ := (35-3*Real.sqrt 70)/50
  let E₀ := ((3*Real.sqrt 70/55:ℝ):ℂ)*(w*(∫ t : ℝ, (w^2-(t:ℂ))⁻¹ ∂μ))
  obtain ⟨hαm,hαm6,hgap,hslack,hαp,hα6p,hgapSE,hgapNE,hloc⟩ := fourth_septic_scalar_gaps
  have hα₀ : 0 < α₀ := by have hh := fourth_sextic_numeric_gaps; dsimp [α₀]; linarith [hh.2.2.1]
  have hα₀up : α₀ < 1/10 := fourth_sextic_numeric_gaps.2.2.2.1
  obtain ⟨hA₀lo,hA₀hi,hB₀hi,hC₀lo,hC₀hi⟩ := fourth_sextic_correction_bounds μ hsupp hμ w hwpos hwim hwX
  change E₀.re/w.re ≤ 391/25000 at hA₀hi
  change E₀.im/w.im ≤ 0 at hB₀hi
  change (3*(E₀.re/w.re)-E₀.im/w.im)/2 ≤ 9/200 at hC₀hi
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  have hg₀ : β/w = (α₀:ℂ)*w^2-(b₀:ℂ)+E₀/w := by
    convert hwinv using 1
    dsimp [α₀,b₀,E₀]
    field_simp
  obtain ⟨hr₀,hi₀,_⟩ := cubic_graph_coordinate_parts β w E₀ α₀ b₀ hw hg₀
  have hR₀ : β.re/w.re = α₀*(w.re^2-3*w.im^2)-b₀+E₀.re/w.re := by rw [hr₀]; field_simp
  have hI₀ : β.im/w.im = α₀*(3*w.re^2-w.im^2)-b₀+E₀.im/w.im := by rw [hi₀]; field_simp
  have hWedge : 10/3 ≤ w.re^2-3*w.im^2 := by
    have hh : 0 ≤ β.re/w.re := div_nonneg hR hwpos.le
    rw [hR₀] at hh
    have ht : α₀*(10/3) < α₀*(w.re^2-3*w.im^2) := by
      change 391/25000 < b₀-(10/3)*α₀ at hslack
      linarith
    exact (lt_of_mul_lt_mul_left ht hα₀.le).le
  let p : Polynomial ℂ := X^7-C 7*X^5-C (35*β)*X^4+C (77/6)*X^3+
    C ((385/4)*β)*X^2+C ((275/2)*β^2-121/24)*X-C ((605/24)*β)
  have hpdeg : p.natDegree = 7 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w=0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 7*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 10/3 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hzroot : (275/2)*β^2*z-35*β*z^4+(385/4)*β*z^2-(605/24)*β+
      z^7-7*z^5+(77/6)*z^3-(121/24)*z=0 := by
    have he := hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at he
    linear_combination he
  obtain ⟨hy0,hzero⟩ := fourth_septic_nonnegative_im β z hR hI.le hx hX hzroot
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fourth_septic_upper_data β z hx hy hX hzroot
  obtain ⟨hr₁,hi₁,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr₁]; field_simp
  have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi₁]; field_simp
  have hslow : α = (7-3*Real.sqrt 3)/55 ∧ b = 7*(3-Real.sqrt 3)/60 ∧ e=septicRemainder z ∧
      0 ≤ (3*(e.re/z.re)-e.im/z.im)/2 := by
    rcases hcases with hs|⟨ha,hb,hAlo,hAhi,hBlo,hBhi⟩
    · exact hs
    · exfalso
      subst α
      subst b
      by_cases hvy : z.im ≤ w.im
      · exact inverse_graph_large_slope_southeast_impossible β.re w.re w.im z.re z.im α₀ _ b₀ _
          (E₀.re/w.re) (e.re/z.re) (10/3) (391/25000) 0 hR hwpos hy.le hxz hvy hWedge
          (by linarith) hα6p hA₀hi hAlo (by simpa [α₀,b₀] using hgapSE) hR₀ hR₁
      · exact fast_graph_northeast_impossible α₀ _ b₀ _ (e.re/z.re) (E₀.im/w.im) (e.im/z.im)
          (10/3) (3/40) β.re β.im w.re w.im z.re z.im hwpos hwim hxz (le_of_not_ge hvy)
          hR hI.le hwX hα₀.le (by linarith) (by linarith) hB₀hi (by linarith) hgapNE hI₀ hR₁ hI₁
  rcases hslow with ⟨rfl,rfl,rfl,hC₁⟩
  have himorder : w.im ≤ z.im := by
    by_contra hn
    have hvy := le_of_not_ge hn
    exact inverse_graph_southeast_impossible α₀ _ b₀ _ (E₀.re/w.re) ((septicRemainder z).re/z.re)
      (E₀.im/w.im) ((septicRemainder z).im/z.im) (9/200) β.re β.im w.re w.im z.re z.im
      (by linarith) hαm6 hwpos hy hxz hvy hR hI.le hC₀hi hC₁ hgap hR₀ hI₀ hR₁ hI₁
  have hX4 : 4 < z.re^2 := by
    have hA := (septic_remainder_coordinate_bounds z hx hy hX).2.1
    have hnonneg : 0 ≤ β.re/z.re := div_nonneg hR hx.le
    rw [hR₁] at hnonneg
    have hterm := mul_nonneg (show 0 ≤ (7-3*Real.sqrt 3)/55 by linarith) (sq_nonneg z.im)
    have ht : ((7-3*Real.sqrt 3)/55)*4 < ((7-3*Real.sqrt 3)/55)*z.re^2 := by
      nlinarith only [hA,hnonneg,hterm,hloc]
    exact lt_of_mul_lt_mul_left ht (by linarith)
  exact ⟨z,hzroot,hxz,himorder,hX4,hgraph⟩
