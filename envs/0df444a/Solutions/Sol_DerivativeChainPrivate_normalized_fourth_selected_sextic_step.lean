-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fourth_selected_sextic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T16:01:02.51003+00:00
-- url     : https://prove2.me/submissions/014d599c-ff9d-429a-8443-73ef1f92c395

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib
import Theorems.Thm_TeschlQM_Herglotz_herglotz_representation
import Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
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

theorem quadrant_phase_forces_nonnegative_im (β z : ℂ) (k : ℝ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hx : 0 < z.re) (hk : 0 < k)
    (hphase : (β / z).im = 2 * z.re * z.im * k) :
    0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hD : 0 < Complex.normSq z := by
    rw [← Complex.sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hquot : (β / z).im * Complex.normSq z = β.im * z.re - β.re * z.im := by
    rw [Complex.div_im]
    field_simp
  rw [hphase] at hquot
  have hcoeff : 0 < 2 * z.re * k * Complex.normSq z + β.re := by positivity
  have hprod : (2 * z.re * k * Complex.normSq z + β.re) * z.im = β.im * z.re := by
    nlinarith only [hquot]
  refine ⟨nonneg_of_mul_nonneg_right (hprod.symm ▸ mul_nonneg hI hx.le) hcoeff, ?_⟩
  intro hzero
  rw [hzero,zero_mul] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff.ne'

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
-- Source module: HermiteVerified

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace DerivativeChainPrivate.Hermite















end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite























end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma root_between (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
    (show (0:ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨ha.le,hb.le⟩)
  refine ⟨x,⟨?_,?_⟩,hroot⟩
  · by_contra hn
    have he : x = a := by linarith [hx.1]
    subst x; linarith
  · by_contra hn
    have he : x = b := by linarith [hx.2]
    subst x; linarith









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite













end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





end DerivativeChainPrivate.Hermite

end


section
-- Source module: SexticAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_sextic_discriminant_identity (β z : ℂ)
    (hroot : (275/14)*β^2 - 20*β*z^3 + (55/2)*β*z +
      z^6 - 5*z^4 + (11/2)*z^2 - 121/168 = 0) :
    (550*β - 280*z^3 + 385*z)^2 =
      (25/3)*(7560*z^6 - 16632*z^4 + 7623*z^2 + 1331) := by
  linear_combination 15400*hroot



theorem fourth_sextic_constant_negative (U : ℝ) (hlo : 5/2 ≤ U) (hhi : U ≤ 10/3) :
    U^3 - 5*U^2 + (11/2)*U - 121/168 < 0 := by
  have hprod := mul_nonneg (mul_nonneg (show 0 ≤ U-5/2 by linarith)
    (show 0 ≤ 10/3-U by linarith)) (show 0 ≤ U+5/6 by linarith)
  nlinarith only [hprod,hlo,hhi]



end DerivativeChainPrivate

end


section
-- Source module: SexticLevels


set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem fourth_sextic_nonnegative_levels_splits (t : ℝ) (ht : 0 ≤ t) :
    (7560*X^3 + (-16632)*X^2 + C (7623-7560*t)*X + 1331 : Polynomial ℝ).Splits := by
  let p : Polynomial ℝ := 7560*X^3 + (-16632)*X^2 + C (7623-7560*t)*X + 1331
  change p.Splits
  have hneg : p.eval (-t-10) < 0 := by
    norm_num [p]
    nlinarith only [ht,pow_nonneg ht 2,pow_nonneg ht 3]
  have hpos : 0 < p.eval (t+10) := by
    norm_num [p]
    nlinarith only [ht,pow_nonneg ht 2,pow_nonneg ht 3]
  obtain ⟨a,ha,hra⟩ := Hermite.root_between p (show -t-10 < 0 by linarith)
    hneg (by norm_num [p])
  obtain ⟨b,hb,hrb⟩ := Hermite.root_between (-p) (show (0 : ℝ) < 1 by norm_num)
    (by norm_num [p]) (by norm_num [p]; linarith)
  have hrb : p.eval b = 0 := by simpa using hrb
  obtain ⟨c,hc,hrc⟩ := Hermite.root_between p (show 1 < t+10 by linarith)
    (by norm_num [p]; linarith) hpos
  let r : Fin 3 → ℝ := ![a,b,c]
  have hinj : Function.Injective r := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [r] at hij ⊢ <;>
      linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2]
  have hr : ∀ i, p.eval (r i) = 0 := by
    intro i
    fin_cases i
    · exact hra
    · exact hrb
    · exact hrc
  let s := Finset.univ.image r
  have hs : s.card = 3 := by simp [s,Finset.card_image_of_injective _ hinj]
  have hdeg : p.natDegree = 3 := by dsimp [p]; compute_degree!
  have hn : p ≠ 0 := by
    intro he
    have := congrArg (fun q : Polynomial ℝ => q.eval 0) he
    norm_num [p] at this
  have heq : p.roots = s.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact hr i
    · omega
    · exact hn
  apply Polynomial.splits_iff_card_roots.mpr
  simpa [heq,hdeg] using hs

theorem fourth_sextic_radicand_avoids_nonnegative (z : ℂ) (hz : 0 < z.im) :
    let H := z^2 + (-11/5 : ℂ)*z + (121/120 : ℂ) + (1331/7560 : ℂ)/z
    H.im ≠ 0 ∨ H.re < 0 := by
  let H := z^2 + (-11/5 : ℂ)*z + (121/120 : ℂ) + (1331/7560 : ℂ)/z
  change H.im ≠ 0 ∨ H.re < 0
  by_contra! hf
  let t := H.re
  have ht : 0 ≤ t := hf.2
  have hH : H = (t : ℂ) := by apply Complex.ext <;> simp [t,hf.1]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let p : Polynomial ℝ := 7560*X^3 + (-16632)*X^2 + C (7623-7560*t)*X + 1331
  have hs : p.Splits := fourth_sextic_nonnegative_levels_splits t ht
  have hp : p ≠ 0 := by
    intro h
    have hh := congrArg (fun q : Polynomial ℝ => q.eval 0) h
    norm_num [p] at hh
  have hr : (p.map Complex.ofRealHom).eval z = 0 := by
    simp only [p,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_X,Polynomial.map_C,Polynomial.map_ofNat,Polynomial.map_neg,
      eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat,eval_neg]
    change 7560*z^3 + (-16632)*z^2 + (((7623-7560*t : ℝ) : ℂ))*z + 1331 = 0
    push_cast
    calc
      _ = 7560*z*(H-(t : ℂ)) := by dsimp only [H]; field_simp; ring
      _ = 0 := by rw [hH]; ring
  obtain ⟨r,he⟩ := hs.mem_range_of_isRoot hp hr
  have hi := congrArg Complex.im he
  change (0 : ℝ) = z.im at hi
  linarith





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

theorem sexticShift_im_ne_zero (a b c : ℝ) (hc : c ≠ 0)
    (hD : ∀ v : ℝ, 0 ≤ ((a/2+v)^2-b)^2+8*c*v)
    (z : ℂ) (hz : 0 < z.im) : (sexticShift a b c z).im ≠ 0 := by
  intro hzero
  let v := (sexticShift a b c z).re
  have hreal : sexticShift a b c z = (v : ℂ) := by apply Complex.ext <;> simp [v,hzero]
  have hF : sexticUpperBranch a b c z = z+((a/2 : ℝ) : ℂ)+(v : ℂ) := by
    dsimp only [sexticShift] at hreal
    linear_combination hreal
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hs := sexticUpperBranch_sq a b c z
  rw [hF] at hs
  have hquad : ((2*v : ℝ) : ℂ)*z^2+(((a/2+v)^2-b : ℝ) : ℂ)*z+((-c : ℝ) : ℂ)=0 := by
    calc
      _ = z*((z+((a/2 : ℝ) : ℂ)+(v : ℂ))^2-sexticRadicand a b c z) := by
        dsimp only [sexticRadicand]
        push_cast
        field_simp
        ring
      _ = 0 := by rw [hs]; ring
  have hd : 0 ≤ ((a/2+v)^2-b)^2-4*(2*v)*(-c) := by
    convert hD v using 1 <;> ring
  have hi := real_quadratic_nonnegative_discriminant_root_im (2*v) ((a/2+v)^2-b) (-c)
    (neg_ne_zero.mpr hc) hd z hquad
  linarith

theorem sexticShift_differentiableAt (a b c : ℝ) (z : ℂ) (hz : 0 < z.im)
    (havoid : (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0) :
    DifferentiableAt ℂ (sexticShift a b c) z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : -sexticRadicand a b c z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases havoid with hi | hr
    · right; simpa using hi
    · left; simpa using neg_pos.mpr hr
  have hh : DifferentiableAt ℂ (sexticRadicand a b c) z := by
    unfold sexticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun w => Complex.sqrt (-sexticRadicand a b c w)) z := by
    simpa only [Function.comp_def, Pi.neg_apply] using
      (Complex.differentiableAt_sqrt hslit).comp z hh.neg
  have hf : DifferentiableAt ℂ (sexticUpperBranch a b c) z := by
    exact (differentiableAt_const Complex.I).mul hs
  exact (hf.sub differentiableAt_id).sub (differentiableAt_const ((a/2 : ℝ) : ℂ))

end DerivativeChainPrivate

end


section
-- Source module: SexticPositive


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_sextic_level_discriminant (v : ℝ) :
    0 ≤ (((-11/5 : ℝ)/2+v)^2-121/120)^2+8*(1331/7560)*v := by
  by_cases hv : 0 ≤ v
  · positivity
  · have hv' : v ≤ 0 := le_of_not_ge hv
    have hv3 : 0 ≤ (-v)^3 := pow_nonneg (neg_nonneg.mpr hv') 3
    nlinarith only [sq_nonneg (2*v+3/20), sq_nonneg v, hv3, sq_nonneg (v^2), hv']



theorem sexticShift_im_I_pos (a b c : ℝ) (hb : 0 ≤ b)
    (hgap : 4*b < (a-c)^2)
    (havoid : (sexticRadicand a b c Complex.I).im ≠ 0 ∨
      (sexticRadicand a b c Complex.I).re < 0) :
    0 < (sexticShift a b c Complex.I).im := by
  have hpos := sexticUpperBranch_im_pos a b c Complex.I havoid
  have hs := sexticUpperBranch_sq a b c Complex.I
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [sexticRadicand, Complex.I_sq, Complex.div_I, Complex.add_re,
    Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,mul_one,one_mul,sub_zero,zero_add,add_zero] at hr hi
  simp only [sexticShift,Complex.sub_im,Complex.I_im,Complex.ofReal_im,sub_zero]
  by_contra h
  have hy : (sexticUpperBranch a b c Complex.I).im ≤ 1 := by linarith
  have hy2 : (sexticUpperBranch a b c Complex.I).im^2 ≤ 1 := by nlinarith
  have hx2 : (sexticUpperBranch a b c Complex.I).re^2 ≤ b := by
    simp only [pow_two,Complex.mul_re] at hr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hy2 (sq_nonneg (sexticUpperBranch a b c Complex.I).re)
  simp only [pow_two,Complex.mul_im] at hi
  have hsquare := congrArg (fun x : ℝ => x^2) hi
  nlinarith only [hsquare,hgap,hprod,hx2]

theorem sexticShift_im_pos (a b c : ℝ) (hc : c ≠ 0) (hb : 0 ≤ b)
    (hgap : 4*b < (a-c)^2)
    (hD : ∀ v : ℝ, 0 ≤ ((a/2+v)^2-b)^2+8*c*v)
    (havoid : ∀ z : ℂ, 0 < z.im →
      (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0)
    (z : ℂ) (hz : 0 < z.im) : 0 < (sexticShift a b c z).im := by
  have hI : 0 < Complex.I.im := by norm_num
  have hseed := sexticShift_im_I_pos a b c hb hgap (havoid _ hI)
  have hcont : ContinuousOn (fun w : ℂ => (sexticShift a b c w).im) {w | 0 < w.im} := by
    intro w hw
    exact (Complex.continuous_im.continuousAt.comp
      (sexticShift_differentiableAt a b c w hw (havoid w hw)).continuousAt).continuousWithinAt
  have hconv : Convex ℝ {w : ℂ | 0 < w.im} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  by_contra h
  have hzle : (sexticShift a b c z).im ≤ 0 := le_of_not_gt h
  obtain ⟨w,hw,hew⟩ := hconv.isPreconnected.intermediate_value hz hI hcont ⟨hzle,le_of_lt hseed⟩
  exact sexticShift_im_ne_zero a b c hc hD w hw hew

end DerivativeChainPrivate

end


section
-- Source module: SexticGrowth


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sexticShift_growth (a b c : ℝ)
    (ha : |a| ≤ 3) (hb : |b| ≤ 2) (hc : |c| ≤ 1)
    (hE : |a^2/4-b| ≤ 2)
    (z : ℂ) (hz : 0 < z.im) (hG : 0 < (sexticShift a b c z).im) :
    ‖sexticShift a b c z‖ ≤ 10/z.im := by
  let F := sexticUpperBranch a b c z
  let G := sexticShift a b c z
  let r := ‖z‖
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hr : 0 < r := norm_pos_iff.mpr hz0
  have hy : z.im ≤ r := Complex.im_le_norm z
  have hF := sexticUpperBranch_sq a b c z
  have hFn : ‖F‖^2 = ‖sexticRadicand a b c z‖ := by
    simpa only [norm_pow] using congrArg norm hF
  have hGn : ‖G‖ ≤ ‖F‖+r+|a|/2 := by
    calc
      ‖G‖ ≤ ‖F-z‖+‖((a/2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖F‖+‖z‖+‖((a/2 : ℝ) : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by simp [r,Complex.norm_real,Real.norm_eq_abs,abs_div]
  have hnF := norm_nonneg F
  have hnG := norm_nonneg G
  apply (le_div_iff₀ hz).mpr
  change ‖G‖*z.im ≤ 10
  by_cases hlarge : 1 ≤ r
  · let D := F+z+((a/2 : ℝ) : ℂ)
    have hDi : 2*z.im ≤ D.im := by
      change 0 < (F-z-((a/2:ℝ):ℂ)).im at hG
      dsimp only [D]
      simp only [Complex.add_im,Complex.sub_im,Complex.ofReal_im] at hG ⊢
      linarith
    have hDn : 2*z.im ≤ ‖D‖ := hDi.trans (Complex.im_le_norm D)
    have hprod : G*D = ((b-a^2/4 : ℝ) : ℂ)+(c : ℂ)/z := by
      dsimp only [G,D,sexticShift,F]
      calc
        _ = (sexticUpperBranch a b c z)^2-z^2-(a:ℂ)*z-((a/2:ℝ):ℂ)^2 := by push_cast; ring
        _ = _ := by rw [hF]; unfold sexticRadicand; push_cast; ring
    have hpn : ‖G‖*‖D‖ ≤ 3 := by
      rw [← norm_mul,hprod]
      calc
        _ ≤ ‖((b-a^2/4:ℝ):ℂ)‖+‖(c:ℂ)/z‖ := norm_add_le _ _
        _ = |a^2/4-b|+|c|/r := by simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]; rfl
        _ ≤ 2+1 := add_le_add hE ((div_le_iff₀ hr).mpr (by nlinarith))
        _ = 3 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hDn hnG
    nlinarith only [hpn,hm]
  · have hsmall : r ≤ 1 := le_of_not_ge hlarge
    have hH : ‖sexticRadicand a b c z‖ ≤ r^2+|a| *r+|b|+|c|/r := by
      unfold sexticRadicand
      calc
        _ ≤ ‖z^2+(a:ℂ)*z+(b:ℂ)‖+‖(c:ℂ)/z‖ := norm_add_le _ _
        _ ≤ ‖z^2+(a:ℂ)*z‖+‖(b:ℂ)‖+‖(c:ℂ)/z‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖z^2‖+‖(a:ℂ)*z‖+‖(b:ℂ)‖+‖(c:ℂ)/z‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by simp [r,norm_pow,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
    have hH' : ‖F‖^2*r ≤ r^3+|a| *r^2+|b| *r+|c| := by
      rw [← hFn] at hH
      have hm := mul_le_mul_of_nonneg_right hH (le_of_lt hr)
      have he : (r^2+|a| *r+|b|+|c|/r)*r = r^3+|a| *r^2+|b| *r+|c| := by field_simp
      rwa [he] at hm
    have hr2 : r^2 ≤ 1 := by nlinarith
    have hr3 : r^3 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hr2 (le_of_lt hr)]
    have ha' : |a| *r^2 ≤ 3 := (mul_le_mul_of_nonneg_left hr2 (abs_nonneg a)).trans (by simpa using ha)
    have hb' : |b| *r ≤ 2 := (mul_le_mul_of_nonneg_left hsmall (abs_nonneg b)).trans (by simpa using hb)
    have hbound : ‖F‖^2*r ≤ 7 := by linarith
    have hrr := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (sq_nonneg ‖F‖) (le_of_lt hr))
    have hFr : ‖F‖*r ≤ 3 := by nlinarith
    have hGr := mul_le_mul_of_nonneg_right hGn (le_of_lt hr)
    have ha2 := mul_le_mul_of_nonneg_right ha (le_of_lt hr)
    have hGy := mul_le_mul_of_nonneg_left hy hnG
    nlinarith only [hFr,hGr,ha2,hGy,hsmall,hr2]

end DerivativeChainPrivate

end


section
-- Source module: SexticMeasure


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory TeschlQM.Herglotz

theorem sexticShift_measure (a b c : ℝ) (hc0 : c ≠ 0) (hb0 : 0 ≤ b)
    (hgap : 4*b < (a-c)^2)
    (hD : ∀ v : ℝ, 0 ≤ ((a/2+v)^2-b)^2+8*c*v)
    (havoid : ∀ z : ℂ, 0 < z.im →
      (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0)
    (ha : |a| ≤ 3) (hb : |b| ≤ 2) (hc : |c| ≤ 1) (hE : |a^2/4-b| ≤ 2) :
    ∃ μ : Measure ℝ, μ Set.univ ≤ ENNReal.ofReal 10 ∧
      ∀ z : ℂ, 0 < z.im → sexticShift a b c z = borelTransform μ z := by
  apply TeschlQM.Herglotz.herglotz_representation
  · constructor
    · intro z hz
      exact (sexticShift_differentiableAt a b c z hz (havoid z hz)).differentiableWithinAt
    · exact sexticShift_im_pos a b c hc0 hb0 hgap hD havoid
  · intro z hz
    exact sexticShift_growth a b c ha hb hc hE z hz
      (sexticShift_im_pos a b c hc0 hb0 hgap hD havoid z hz)

theorem fourth_sextic_positive_measure :
    ∃ μ : Measure ℝ, μ Set.univ ≤ ENNReal.ofReal 10 ∧
      ∀ z : ℂ, 0 < z.im →
        sexticShift (-11/5) (121/120) (1331/7560) z = borelTransform μ z := by
  apply sexticShift_measure (-11/5) (121/120) (1331/7560)
    (by norm_num) (by norm_num) (by norm_num) fourth_sextic_level_discriminant
  · intro z hz
    simpa [sexticRadicand] using fourth_sextic_radicand_avoids_nonnegative z hz
  all_goals norm_num



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

theorem sexticUpperBranch_eq_neg_sqrt_of_im_neg (a b c : ℝ) (z : ℂ)
    (hi : (sexticRadicand a b c z).im < 0) :
    sexticUpperBranch a b c z = -Complex.sqrt (sexticRadicand a b c z) := by
  have hF := sexticUpperBranch_im_pos a b c z (Or.inl (ne_of_lt hi))
  have hS := (sqrt_im_sign _ (ne_of_lt hi)).2
  have hSneg : (Complex.sqrt (sexticRadicand a b c z)).im < 0 := by nlinarith
  have hs : (Complex.sqrt (sexticRadicand a b c z))^2 = sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ((sexticUpperBranch_sq a b c z).trans hs.symm) with h|h
  · have hh := congrArg Complex.im h
    linarith
  · exact h

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

theorem sexticRadicand_im_left (a b c : ℝ) (ha : a < 0) (hc : 0 < c)
    (z : ℂ) (hx : z.re ≤ -1/4) (hy : 0 < z.im) :
    (sexticRadicand a b c z).im < 0 := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hy
  have hd : 0 < z.re^2+z.im^2 := by positivity
  have hf : 2*z.re+a < 0 := by linarith
  have hp := mul_neg_of_neg_of_pos hf hd
  have hfneg : (2*z.re+a)*(z.re^2+z.im^2)-c < 0 := by linarith
  have hi := sexticRadicand_im_identity a b c z hz0
  have hm := mul_neg_of_pos_of_neg hy hfneg
  nlinarith

end DerivativeChainPrivate

end


section
-- Source module: MeasureBoundary


set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology

theorem measure_Icc_zero_of_real_extension (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) (E : ℂ → ℂ) (hE : Continuous E)
    (hreal : ∀ t : ℝ, (E (t : ℂ)).im = 0)
    (heq : ∀ t ∈ Icc a b, ∀ ε : ℝ, 0 < ε →
      E ((t : ℂ)+(ε : ℂ)*Complex.I) =
        TeschlQM.Herglotz.borelTransform μ ((t : ℂ)+(ε : ℂ)*Complex.I)) :
    μ (Icc a b) = 0 := by
  have hc : Continuous (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (E ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) := by
    apply Continuous.const_mul
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_im.comp (hE.comp (by fun_prop))
  have hz : (1/Real.pi)*(∫ t in a..b, (E ((t:ℂ)+(0:ℂ)*Complex.I)).im) = 0 := by
    simp [hreal]
  have hlim : Tendsto (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (E ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero,hz] using (hc.tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim' := TeschlQM.Herglotz.stieltjes_inversion_formula μ a b hab
  have hsame : (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (E ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform μ ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    exact congrArg Complex.im (heq t ht ε hε)
  have hv := tendsto_nhds_unique (hlim.congr' hsame) hlim'
  have hto : (μ (Icc a b)).toReal = 0 := by
    have h1 := ENNReal.toReal_nonneg (a := μ (Ioo a b))
    have h2 := ENNReal.toReal_nonneg (a := μ (Icc a b))
    linarith
  exact (ENNReal.toReal_eq_zero_iff _).mp hto |>.resolve_right (measure_ne_top μ _)

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

theorem sexticExteriorExtension_real (a b c σ : ℝ) (f : ℝ → ℝ)
    (hr : ∀ x, 0 < (f x)^2+a*(f x)+b+c/(f x)) (x : ℝ) :
    (sexticExteriorExtension a b c σ f (x:ℂ)).im = 0 := by
  simp only [sexticExteriorExtension,Complex.ofReal_re,Complex.ofReal_im,
    Complex.ofReal_zero,mul_zero,add_zero,sexticRadicand_real]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast (hr x).le)]
  simp

theorem sextic_measure_exterior_intervals (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ z : ℂ, 0 < z.im → sexticShift a b c z = TeschlQM.Herglotz.borelTransform μ z)
    (L U : ℝ) (hLU : L < U) (hside : U ≤ -1/4 ∨ 3/2 ≤ L) :
    μ (Icc L U) = 0 := by
  rcases hside with hl | hr
  · let f : ℝ → ℝ := fun x => min (-1/4) x
    have hf : ∀ x, f x ≤ -1/4 := fun x => min_le_left _ _
    have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
    have hE := sexticExteriorExtension_continuous a b c (-1) f (by dsimp [f]; fun_prop) hf0
      (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
        (Or.inl (by simpa using hf z.re)))
    apply measure_Icc_zero_of_real_extension μ L U hLU (sexticExteriorExtension a b c (-1) f) hE
    · exact sexticExteriorExtension_real a b c (-1) f (fun x => hreal _ (Or.inl (hf x)))
    · intro t ht ε hε
      have ht' : t ≤ -1/4 := ht.2.trans hl
      have hfr : f t = t := min_eq_right ht'
      have hz : 0 < ((t:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
      rw [← hμ _ hz]
      unfold sexticExteriorExtension sexticShift
      simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        zero_mul,zero_add,sub_zero,add_zero,hfr,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul]
      rw [sexticUpperBranch_eq_neg_sqrt_of_im_neg a b c _
        (sexticRadicand_im_left a b c ha0 hc _ (by simpa) hz)]
      congr 2 <;> ring
  · let f : ℝ → ℝ := fun x => max (3/2) x
    have hf : ∀ x, 3/2 ≤ f x := fun x => le_max_left _ _
    have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
    have hE := sexticExteriorExtension_continuous a b c 1 f (by dsimp [f]; fun_prop) hf0
      (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
        (Or.inr (by simpa using hf z.re)))
    apply measure_Icc_zero_of_real_extension μ L U hLU (sexticExteriorExtension a b c 1 f) hE
    · exact sexticExteriorExtension_real a b c 1 f (fun x => hreal _ (Or.inr (hf x)))
    · intro t ht ε hε
      have ht' : 3/2 ≤ t := hr.trans ht.1
      have hfr : f t = t := max_eq_right ht'
      have hz : 0 < ((t:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
      rw [← hμ _ hz]
      unfold sexticExteriorExtension sexticShift
      simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        zero_mul,zero_add,sub_zero,add_zero,hfr,Complex.ofReal_one,one_mul]
      rw [sexticUpperBranch_eq_sqrt_of_im_pos a b c _
        (sexticRadicand_im_right a b c ha hc1 _ (by simpa) hz)]
      congr 2 <;> ring

end DerivativeChainPrivate

end


section
-- Source module: SexticCompactMeasure


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem sextic_measure_ae_interval (μ : Measure ℝ)
    (hi : ∀ L U : ℝ, L < U → U ≤ -1/4 ∨ 3/2 ≤ L → μ (Icc L U) = 0) :
    ∀ᵐ x ∂μ, x ∈ Icc (-1/4 : ℝ) (3/2) := by
  let s : ℕ → Set ℝ := fun n => Icc (-(n+1:ℝ)) (-1/4) ∪ Icc (3/2) (n+2:ℝ)
  have hs : ∀ n, μ (s n) = 0 := by
    intro n
    apply measure_union_null
    · exact hi _ _ (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (Or.inl le_rfl)
    · exact hi _ _ (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (Or.inr le_rfl)
  have hu : μ (⋃ n, s n) = 0 := measure_iUnion_null hs
  apply ae_iff.mpr
  apply measure_mono_null (t := ⋃ n, s n) _ hu
  intro x hx
  change ¬(-1/4 ≤ x ∧ x ≤ 3/2) at hx
  obtain ⟨n,hn⟩ := exists_nat_gt |x|
  apply mem_iUnion.mpr
  refine ⟨n,?_⟩
  dsimp only [s]
  rcases not_and_or.mp hx with h|h
  · left
    constructor
    · have := neg_abs_le x; linarith
    · linarith
  · right
    constructor
    · linarith
    · have := le_abs_self x; linarith

theorem fourth_sextic_compact_positive_measure :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ x ∂μ, x ∈ Icc (-1/4 : ℝ) (3/2)) ∧
      ∀ z : ℂ, 0 < z.im →
        sexticShift (-11/5) (121/120) (1331/7560) z = TeschlQM.Herglotz.borelTransform μ z := by
  obtain ⟨μ,hm,hrep⟩ := fourth_sextic_positive_measure
  haveI : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hm ENNReal.ofReal_lt_top⟩
  refine ⟨μ,inferInstance,?_,hrep⟩
  apply sextic_measure_ae_interval μ
  exact sextic_measure_exterior_intervals (-11/5) (121/120) (1331/7560)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    fourth_sextic_real_exterior μ hrep



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

theorem fast_graph_southeast_impossible (R x y r v α b b₀ A₀ A₁ : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hv : 0 ≤ v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hWedge : 5/2 ≤ x^2-3*y^2) (hα : 9/10 < α) (hb : b < 3/2) (hb₀ : 1/4 ≤ b₀)
    (hA₀ : A₀ ≤ 3/100) (hA₁ : -(3/100) ≤ A₁)
    (hR₀ : R/x = (1/10)*(x^2-3*y^2)-b₀+A₀)
    (hR₁ : R/r = α*(r^2-3*v^2)-b+A₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  rw [hR₀,hR₁] at hreal
  have hsqx : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hsqy : v^2 ≤ y^2 := by nlinarith only [hv,hvy]
  have hdiff : 0 ≤ (r^2-3*v^2)-(x^2-3*y^2) := by linarith only [hsqx,hsqy]
  have hmul := mul_nonneg (show 0 ≤ α by linarith only [hα]) hdiff
  have hprod := mul_le_mul (show (4/5:ℝ) ≤ α-1/10 by linarith only [hα]) hWedge
    (by norm_num : (0:ℝ) ≤ 5/2) (show 0 ≤ α-1/10 by linarith only [hα])
  nlinarith only [hreal,hmul,hprod,hb,hb₀,hA₀,hA₁]

end DerivativeChainPrivate

namespace DerivativeChainPrivate



end DerivativeChainPrivate

end


section
-- Source module: FourthSexticGraphs


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory

theorem fourth_sextic_upper_graphs (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im)
    (hroot : (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0) :
    let J := ∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ
    β/z = (((28-3*Real.sqrt 70)/55:ℝ):ℂ)*z^2-
      (((35-3*Real.sqrt 70)/50:ℝ):ℂ)+((3*Real.sqrt 70/55:ℝ):ℂ)*J ∨
    β/z = (((28+3*Real.sqrt 70)/55:ℝ):ℂ)*z^2-
      (((35+3*Real.sqrt 70)/50:ℝ):ℂ)-((3*Real.sqrt 70/55:ℝ):ℂ)*J := by
  let F := sexticUpperBranch (-11/5) (121/120) (1331/7560) (z^2)
  let s : ℂ := (Real.sqrt 70:ℂ)
  let J := ∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hu : 0 < (z^2).im := by simp [pow_two,Complex.mul_im]; positivity
  have hs : s^2 = 70 := by dsimp [s]; rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hF : F^2 = z^4+(-11/5:ℂ)*z^2+121/120+(1331/7560:ℂ)/z^2 := by
    have ht := sexticUpperBranch_sq (-11/5) (121/120) (1331/7560) (z^2)
    simpa [F,sexticRadicand,← pow_mul] using ht
  have hJ : F = z^2-11/10-J := by
    have ht := hμ (z^2) hu
    have hi : TeschlQM.Herglotz.borelTransform μ (z^2) = -J := by
      unfold TeschlQM.Herglotz.borelTransform
      dsimp only [J]
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [← neg_sub,inv_neg])
    rw [hi] at ht
    dsimp only [sexticShift] at ht
    norm_num [F] at ht ⊢
    linear_combination ht
  have hd := fourth_sextic_discriminant_identity β z hroot
  have hsquare : (30*s*z*F)^2 = (25/3)*(7560*z^6-16632*z^4+7623*z^2+1331) := by
    calc
      _ = 900*s^2*z^2*F^2 := by ring
      _ = _ := by rw [hs,hF]; field_simp; ring
  have hsplit := (sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  dsimp only
  rcases hsplit with hp|hm
  · right
    apply (div_eq_iff hz).mpr
    rw [hJ] at hp
    dsimp only [s] at hp
    push_cast
    linear_combination (1/550:ℂ)*hp
  · left
    apply (div_eq_iff hz).mpr
    rw [hJ] at hm
    dsimp only [s] at hm
    push_cast
    linear_combination (1/550:ℂ)*hm

end DerivativeChainPrivate

end


section
-- Source module: FourthSexticScalars


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_sextic_bound_at_five_halves :
    (5/2:ℝ)+(-11/5)/2-Real.sqrt ((5/2)^2+(-11/5)*(5/2)+121/120+(1331/7560)/(5/2)) < 1/20 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (5/2)^2+(-11/5)*(5/2)+121/120+(1331/7560)/(5/2))
  have hp := Real.sqrt_nonneg ((5/2:ℝ)^2+(-11/5)*(5/2)+121/120+(1331/7560)/(5/2))
  norm_num at hs hp ⊢
  nlinarith

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
-- Source module: FourthSexticUpperData


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem fourth_sextic_upper_data (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 5/2 ≤ z.re^2)
    (hroot : (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0) :
    ∃ α b : ℝ, ∃ e : ℂ,
      1/20 < α ∧ β/z = (α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((α = (28-3*Real.sqrt 70)/55 ∧ b = (35-3*Real.sqrt 70)/50 ∧
        e = ((3*Real.sqrt 70/55:ℝ):ℂ)*(z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)) ∧
        α < 1/10 ∧ 3/50 < 23/80-b ∧ 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2) ∨
       (9/10 < α ∧ b < 5/4 ∧ -(1/40) ≤ e.re/z.re ∧ e.re/z.re ≤ 0 ∧ 0 ≤ e.im/z.im)) := by
  let s := Real.sqrt 70
  let k := 3*s/55
  let J := ∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ
  let E := z*J
  let M := ∫ t : ℝ, 1/((5/2)-t) ∂μ
  have hMeq : M = (5/2:ℝ)+(-11/5)/2-
      Real.sqrt ((5/2)^2+(-11/5)*(5/2)+121/120+(1331/7560)/(5/2)) := by
    have hb := sextic_measure_real_value (-11/5) (121/120) (1331/7560)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fourth_sextic_real_exterior μ hsupp hμ (5/2) (by norm_num)
    have ht := real_cauchy_integral_of_borel_value μ (5/2) _ hb
    dsimp only [M]
    linarith only [ht]
  have hMlt : M < 1/20 := by rw [hMeq]; exact fourth_sextic_bound_at_five_halves
  obtain ⟨hA0,hAM,hC⟩ := cauchy_root_corrections μ hsupp z hx hy (5/2) (by norm_num) hX
  obtain ⟨hB0,hBM⟩ := cauchy_root_imaginary_bounds μ hsupp z hx hy (5/2) (by norm_num) hX
  change 0 ≤ E.re/z.re at hA0
  change E.re/z.re ≤ M at hAM
  change 0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 at hC
  change E.im/z.im ≤ 0 at hB0
  change -(1+3/((5/2:ℝ)-3/2))*M ≤ E.im/z.im at hBM
  norm_num at hBM
  have hM0 : 0 ≤ M := hA0.trans hAM
  obtain ⟨hk,hkhalf,hαm,hαmup,hαp,hbp,hgap,hbm⟩ := fourth_sextic_numeric_gaps
  change 0 < k at hk
  change k < 1/2 at hkhalf
  have hkM : k*M < 1/40 := by nlinarith only [hkhalf,hMlt,hk,hM0]
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hAre : ((k:ℂ)*E).re/z.re = k*(E.re/z.re) := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; ring
  have hBim : ((k:ℂ)*E).im/z.im = k*(E.im/z.im) := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; ring
  have hAupper : ((k:ℂ)*E).re/z.re ≤ 1/40 := by rw [hAre]; nlinarith only [mul_le_mul_of_nonneg_left hAM hk.le,hkM]
  have hBlower : -(1/10) ≤ ((k:ℂ)*E).im/z.im := by rw [hBim]; nlinarith only [mul_le_mul_of_nonneg_left hBM hk.le,hkM]
  have hApos : 0 ≤ ((k:ℂ)*E).re/z.re := by rw [hAre]; positivity
  have hBneg : ((k:ℂ)*E).im/z.im ≤ 0 := by rw [hBim]; exact mul_nonpos_of_nonneg_of_nonpos hk.le hB0
  rcases fourth_sextic_upper_graphs μ hμ β z hx hy hroot with hm|hp
  · have hg : β/z = (((28-3*s)/55:ℝ):ℂ)*z^2-(((35-3*s)/50:ℝ):ℂ)+((k:ℂ)*E)/z := by
      convert hm using 1
      dsimp only [E,J,k,s]
      field_simp <;> ring
    refine ⟨(28-3*s)/55,(35-3*s)/50,(k:ℂ)*E,hαm,hg,?_,Or.inl ⟨rfl,rfl,rfl,hαmup,hgap,?_⟩⟩
    · exact cubic_graph_positive_phase_of_corrections β z ((k:ℂ)*E) _ _ (1/40) hx hy hX
        (by norm_num) (by linarith only [hαm]) hAupper (by convert hBlower using 1 <;> norm_num) hg
    · rw [hAre,hBim]
      have hp := mul_nonneg hk.le hC
      nlinarith only [hp]
  · have hg : β/z = (((28+3*s)/55:ℝ):ℂ)*z^2-(((35+3*s)/50:ℝ):ℂ)+(-((k:ℂ)*E))/z := by
      convert hp using 1
      dsimp only [E,J,k,s]
      field_simp <;> ring
    have hAn : (-((k:ℂ)*E)).re/z.re = -(((k:ℂ)*E).re/z.re) := by simp only [Complex.neg_re,neg_div]
    have hBn : (-((k:ℂ)*E)).im/z.im = -(((k:ℂ)*E).im/z.im) := by simp only [Complex.neg_im,neg_div]
    refine ⟨(28+3*s)/55,(35+3*s)/50,-((k:ℂ)*E),by linarith only [hαp],hg,?_,
      Or.inr ⟨hαp,hbp,?_,?_,?_⟩⟩
    · apply cubic_graph_positive_phase_of_corrections β z (-((k:ℂ)*E)) _ _ (1/40) hx hy hX
        (by norm_num) (by linarith only [hαp]) _ _ hg
      · rw [hAn]; linarith only [hApos]
      · rw [hBn]; linarith only [hBneg]
    · rw [hAn]; linarith only [hAupper]
    · rw [hAn]; linarith only [hApos]
    · rw [hBn]; linarith only [hBneg]

end DerivativeChainPrivate

end


section
-- Source module: FourthSexticPhase


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem fourth_sextic_real_root_parameter (β : ℂ) (x : ℝ) (hx : 0 < x) (hX : 5/2 ≤ x^2)
    (hroot : (275/14)*β^2-20*β*(x:ℂ)^3+(55/2)*β*(x:ℂ)+(x:ℂ)^6-5*(x:ℂ)^4+
      (11/2)*(x:ℂ)^2-121/168=0) : β.im = 0 := by
  let A : ℝ := 275/14
  let B : ℝ := -20*x^3+(55/2)*x
  let C : ℝ := x^6-5*x^4+(11/2)*x^2-121/168
  have hquad : (A:ℂ)*β^2+(B:ℂ)*β+(C:ℂ)=0 := by
    dsimp [A,B,C]; push_cast; linear_combination hroot
  have hH := fourth_sextic_real_exterior (x^2) (Or.inr (by linarith))
  have hid : B^2-4*A*C = (2250/7)*x^2*(x^4+(-11/5)*x^2+121/120+(1331/7560)/x^2) := by
    dsimp [A,B,C]
    field_simp
    ring
  have hd : 0 ≤ B^2-4*A*C := by
    rw [hid]
    have hh : 0 < x^4+(-11/5)*x^2+121/120+(1331/7560)/x^2 := by
      convert hH using 1 <;> ring
    positivity
  by_cases hC : C ≠ 0
  · exact real_quadratic_nonnegative_discriminant_root_im A B C hC hd β hquad
  · have hC0 := not_ne_iff.mp hC
    rw [hC0,Complex.ofReal_zero,add_zero] at hquad
    have hp : β*((A:ℂ)*β+(B:ℂ))=0 := by linear_combination hquad
    rcases mul_eq_zero.mp hp with he|he
    · simp [he]
    · have hi := congrArg Complex.im he
      norm_num [A] at hi
      linarith

theorem fourth_sextic_nonnegative_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hroot : (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0) :
    0 ≤ z.im ∧ (β.im = 0 ↔ z.im = 0) := by
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hnonneg : 0 ≤ z.im := by
    by_contra h
    have hy : z.im < 0 := lt_of_not_ge h
    have hroot' : (275/14)*(starRingEnd ℂ β)^2-20*(starRingEnd ℂ β)*(starRingEnd ℂ z)^3+
        (55/2)*(starRingEnd ℂ β)*(starRingEnd ℂ z)+(starRingEnd ℂ z)^6-5*(starRingEnd ℂ z)^4+
        (11/2)*(starRingEnd ℂ z)^2-121/168=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,map_div₀,map_ofNat,map_zero] using congrArg (starRingEnd ℂ) hroot
    obtain ⟨α,b,e,_,_,hp,_⟩ := fourth_sextic_upper_data μ hsupp hμ (starRingEnd ℂ β)
      (starRingEnd ℂ z) (by simpa using hx) (by simpa using neg_pos.mpr hy) (by simpa using hX) hroot'
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
    obtain ⟨α,b,e,_,_,hp,_⟩ := fourth_sextic_upper_data μ hsupp hμ β z hx hy hX hroot
    have hn : (β/z).im ≤ 0 := by
      rw [Complex.div_im,← sub_div,hβ,zero_mul,zero_sub]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hR hy.le]) (Complex.normSq_nonneg z)
    linarith
  · intro hy
    have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hy]
    rw [he] at hroot
    exact fourth_sextic_real_root_parameter β z.re hx hX hroot

end DerivativeChainPrivate

end


section
-- Source module: FourthQuinticEstimates


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fourth_quintic_estimates (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < w.re) (hy : 0 ≤ w.im) (hX : 5/2 ≤ w.re^2)
    (hinv : β/w = (1/10:ℂ)*w^2-23/80+(33/640:ℂ)/(w^2-11/24)) :
    let U := w.re^2+w.im^2
    let D := ‖w^2-(11/24:ℂ)‖^2
    let A := (33/640:ℝ)*(U-11/24)/D
    let B := -(33/640:ℝ)*(U+11/24)/D
    0 ≤ A ∧ A ≤ 3/100 ∧ B ≤ 0 ∧ (3*A-B)/2 ≤ 3/50 ∧
      5/2 ≤ w.re^2-3*w.im^2 ∧
      β.re/w.re = (1/10:ℝ)*(w.re^2-3*w.im^2)-23/80+A ∧
      (0 < w.im → β.im/w.im = (1/10:ℝ)*(3*w.re^2-w.im^2)-23/80+B) ∧
      (β.im=0 → w.im=0) := by
  let U := w.re^2+w.im^2
  let D := ‖w^2-(11/24:ℂ)‖^2
  let A := (33/640:ℝ)*(U-11/24)/D
  let B := -(33/640:ℝ)*(U+11/24)/D
  have hU : 5/2 ≤ U := by dsimp [U]; nlinarith [sq_nonneg w.im]
  have hUc : 0 < U-11/24 := by linarith
  have hw : w ≠ 0 := by intro h; simp [h] at hx
  have hpole : w^2-(11/24:ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    have hi0 : w.im = 0 := by nlinarith
    nlinarith [hX]
  obtain ⟨hr,hi,hphase,hd⟩ := rational_inverse_parts β w (1/10) (23/80) (33/640) (11/24)
    hw (by norm_num; exact hpole) (by norm_num; exact hinv)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hr hi hphase hd
  have hDlow : (U-11/24)^2 ≤ D := by dsimp only [U,D]; nlinarith only [hd,sq_nonneg w.im]
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hUc) hDlow
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hAu : A ≤ 3/100 := by
    dsimp only [A]
    apply (div_le_iff₀ hDp).mpr
    nlinarith [sq_nonneg (U-5/2)]
  have hB0 : B ≤ 0 := by dsimp only [B]; apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith
  have hC : (3*A-B)/2 ≤ 3/50 := by
    have he : (3*A-B)/2 = (33/640:ℝ)*(2*U-11/24)/D := by dsimp [A,B]; ring
    rw [he]
    apply (div_le_iff₀ hDp).mpr
    nlinarith [sq_nonneg (U-5/2)]
  have hRpart : β.re/w.re = (1/10:ℝ)*(w.re^2-3*w.im^2)-23/80+A := by
    rw [hr]
    dsimp only [A,U,D]
    field_simp
  have hW : 5/2 ≤ w.re^2-3*w.im^2 := by
    have hh : 0 ≤ β.re/w.re := div_nonneg hR hx.le
    rw [hRpart] at hh
    linarith only [hh,hAu]
  have hphasepos : 0 < (1/10:ℝ)-(33/640)/D := by
    have hD1 : 1 < D := by nlinarith
    have hb : (33/640:ℝ)/D ≤ 33/640 := by
      apply (div_le_iff₀ hDp).mpr
      linarith
    linarith
  have hzero := (quadrant_phase_forces_nonnegative_im β w _ hR hI hx hphasepos hphase).2
  refine ⟨hA0,hAu,hB0,hC,hW,hRpart,?_,hzero⟩
  intro hypos
  rw [hi]
  field_simp <;> ring

end DerivativeChainPrivate

end


section
-- Source module: FourthSexticStep


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial MeasureTheory

theorem normalized_fourth_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(11/6)*w+(55/12)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-23/80+(33/640:ℂ)/(w^2-11/24)) :
    ∃ z : ℂ,
      (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im := by
  obtain ⟨μ,hfinite,hsupp,hμ⟩ := fourth_sextic_compact_positive_measure
  letI : IsFiniteMeasure μ := hfinite
  obtain ⟨hAw0,hAw,hBw,hCw,hWedge,hR₀,hI₀,hwzero⟩ :=
    fourth_quintic_estimates β w hR hI hwpos hwim hwX hwinv
  let A₀ := (33/640:ℝ)*(w.re^2+w.im^2-11/24)/‖w^2-(11/24:ℂ)‖^2
  let B₀ := -(33/640:ℝ)*(w.re^2+w.im^2+11/24)/‖w^2-(11/24:ℂ)‖^2
  let p : Polynomial ℂ := X^6-C 5*X^4-C (20*β)*X^3+C (11/2)*X^2+
    C ((55/2)*β)*X+C ((275/14)*β^2-121/168)
  have hpdeg : p.natDegree = 6 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w=0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 6*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hzroot : (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0 := by
    have he := hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at he
    linear_combination he
  obtain ⟨hzim,hzero⟩ := fourth_sextic_nonnegative_im μ hsupp hμ β z hR hI hx hX hzroot
  refine ⟨z,hzroot,hxz,?_⟩
  by_contra h
  have hlt : z.im < w.im := lt_of_not_ge h
  by_cases hzi : z.im=0
  · have hβzero := hzero.mpr hzi
    have := hwzero hβzero
    linarith
  · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzi)
    have hy : 0 < w.im := lt_trans hv hlt
    obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fourth_sextic_upper_data μ hsupp hμ β z hx hv hX hzroot
    obtain ⟨hr,hi,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
    have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr]; field_simp
    have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi]; field_simp
    rcases hcases with ⟨_,_,_,hslow,hgap,hCnonneg⟩ | ⟨hfast,hbup,hAlower,_,_⟩
    · exact inverse_graph_southeast_impossible (1/10) α (23/80) b A₀ (e.re/z.re) B₀ (e.im/z.im)
        (3/50) β.re β.im w.re w.im z.re z.im (by linarith) hslow hwpos hv hxz hlt.le
        hR hI hCw hCnonneg hgap hR₀ (hI₀ hy) hR₁ hI₁
    · exact fast_graph_southeast_impossible β.re w.re w.im z.re z.im α b (23/80) A₀ (e.re/z.re)
        hR hwpos hv.le hxz hlt.le hWedge hfast (by linarith) (by norm_num)
        hAw (by linarith) hR₀ hR₁

end DerivativeChainPrivate

end


section
-- Source module: FourthSexticSelected


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem fourth_sextic_selected_graph (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β w z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwinv : β/w = (1/10:ℂ)*w^2-23/80+(33/640:ℂ)/(w^2-11/24))
    (hxz : w.re ≤ z.re) (hzI : 0 < z.im)
    (hzroot : (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0) :
    β/z = (((28-3*Real.sqrt 70)/55:ℝ):ℂ)*z^2-(((35-3*Real.sqrt 70)/50:ℝ):ℂ)+
      ((3*Real.sqrt 70/55:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hxz]
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hw : w ≠ 0 := by intro he; simp [he] at hwpos
  have hy : 0 < w.im := by
    by_contra hn
    have hw0 : w.im=0 := le_antisymm (le_of_not_gt hn) hwim
    have hwreal : w = (w.re:ℂ) := by apply Complex.ext <;> simp [hw0]
    have heq := (div_eq_iff hw).mp hwinv
    rw [hwreal] at heq
    have hi := congrArg Complex.im heq
    norm_num [Complex.mul_im,Complex.mul_re,Complex.div_im,pow_two] at hi
    have hzero := (fourth_sextic_nonnegative_im μ hsupp hμ β z hR hI hx hX hzroot).2.mp hi
    linarith
  obtain ⟨hAw0,hAw,hBw,hCw,hWedge,hR₀,hI₀,_⟩ :=
    fourth_quintic_estimates β w hR hI hwpos hwim hwX hwinv
  let A₀ := (33/640:ℝ)*(w.re^2+w.im^2-11/24)/‖w^2-(11/24:ℂ)‖^2
  let B₀ := -(33/640:ℝ)*(w.re^2+w.im^2+11/24)/‖w^2-(11/24:ℂ)‖^2
  obtain ⟨α,b,e,hα,hgraph,_,hcases⟩ := fourth_sextic_upper_data μ hsupp hμ β z hx hzI hX hzroot
  rcases hcases with ⟨ha,hb,he,_,_,_⟩ | ⟨hfast,hbup,hAlower,hAup,hBlo⟩
  · rw [ha,hb,he] at hgraph
    convert hgraph using 1
    field_simp
  · exfalso
    obtain ⟨hr,hi,_⟩ := cubic_graph_coordinate_parts β z e α b hz hgraph
    have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+e.re/z.re := by rw [hr]; field_simp
    have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+e.im/z.im := by rw [hi]; field_simp
    by_cases hvy : z.im ≤ w.im
    · exact fast_graph_southeast_impossible β.re w.re w.im z.re z.im α b (23/80) A₀ (e.re/z.re)
        hR hwpos hzI.le hxz hvy hWedge hfast (by linarith) (by norm_num)
        hAw (by linarith) hR₀ hR₁
    · exact fast_graph_northeast_impossible (1/10) α (23/80) b (e.re/z.re) B₀ (e.im/z.im)
        (5/2) 0 β.re β.im w.re w.im z.re z.im hwpos hy hxz (le_of_not_ge hvy) hR hI hwX
        (by norm_num) (by linarith) (by linarith) hBw (by linarith) (by linarith) (hI₀ hy) hR₁ hI₁

end DerivativeChainPrivate

end


section
-- Source module: FourthSexticLocalization


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem fourth_sextic_real_graph_negative (X : ℝ) (hlo : 5/2 ≤ X) (hhi : X ≤ 10/3) :
    ((28-3*Real.sqrt 70)/55)*X-(35-3*Real.sqrt 70)/50+
      (3*Real.sqrt 70/55)*(X+(-11/5)/2-Real.sqrt (X^2+(-11/5)*X+121/120+(1331/7560)/X)) < 0 := by
  let H := X^2+(-11/5)*X+121/120+(1331/7560)/X
  let k := 3*Real.sqrt 70/55
  let L := (28/55:ℝ)*X-7/10
  have hX : 0 < X := by linarith
  have hH : 0 < H := fourth_sextic_real_exterior X (Or.inr (by linarith))
  have hk : 0 < k := by dsimp [k]; positivity
  have hL : 0 < L := by dsimp [L]; linarith
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 70)
  have hq := Real.sq_sqrt hH.le
  have hk2 : k^2 = 126/605 := by
    dsimp only [k]
    rw [div_pow,mul_pow,hs]
    norm_num
  have hid : (k*Real.sqrt H)^2-L^2 =
      -(14/275)*(X^3-5*X^2+(11/2)*X-121/168)/X := by
    rw [mul_pow,hk2,hq]
    dsimp only [L,H]
    field_simp
    ring
  have hC := fourth_sextic_constant_negative X hlo hhi
  have hpos : 0 < -(14/275:ℝ)*(X^3-5*X^2+(11/2)*X-121/168)/X := by exact div_pos (mul_pos_of_neg_of_neg (by norm_num) hC) hX
  have hkp : 0 < k*Real.sqrt H := mul_pos hk (Real.sqrt_pos.mpr hH)
  have hlt : L < k*Real.sqrt H := by nlinarith only [hid,hpos,hkp,hL]
  have he : ((28-3*Real.sqrt 70)/55)*X-(35-3*Real.sqrt 70)/50+
      (3*Real.sqrt 70/55)*(X+(-11/5)/2-Real.sqrt (X^2+(-11/5)*X+121/120+(1331/7560)/X)) =
      L-k*Real.sqrt H := by dsimp [L,k,H]; ring
  rw [he]
  linarith

theorem fourth_sextic_selected_localization (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hR : 0 ≤ β.re) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 5/2 ≤ z.re^2)
    (hgraph : β/z = (((28-3*Real.sqrt 70)/55:ℝ):ℂ)*z^2-(((35-3*Real.sqrt 70)/50:ℝ):ℂ)+
      ((3*Real.sqrt 70/55:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)) : 10/3 < z.re^2 := by
  let k := 3*Real.sqrt 70/55
  let α := (28-3*Real.sqrt 70)/55
  let b := (35-3*Real.sqrt 70)/50
  let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
  let M := ∫ t : ℝ, 1/(z.re^2-t) ∂μ
  have hk : 0 < k := by dsimp [k]; positivity
  have hα : 0 < α := by have hh := fourth_sextic_numeric_gaps; dsimp [α]; linarith [hh.2.2.1]
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hg : β/z = (α:ℂ)*z^2-(b:ℂ)+((k:ℂ)*E)/z := by
    convert hgraph using 1
    dsimp [α,b,k,E]
    field_simp
  have hr := (cubic_graph_coordinate_parts β z ((k:ℂ)*E) α b hz hg).1
  have hRpart : β.re/z.re = α*(z.re^2-3*z.im^2)-b+k*(E.re/z.re) := by
    rw [hr]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    field_simp
  have hA := (cauchy_root_corrections μ hsupp z hx hy (z.re^2) hX le_rfl).2.1
  change E.re/z.re ≤ M at hA
  have hM : M = z.re^2+(-11/5)/2-Real.sqrt (z.re^4+(-11/5)*z.re^2+121/120+(1331/7560)/z.re^2) := by
    have hb := sextic_measure_real_value (-11/5) (121/120) (1331/7560)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fourth_sextic_real_exterior μ hsupp hμ (z.re^2) (by linarith)
    have ht := real_cauchy_integral_of_borel_value μ (z.re^2) _ hb
    dsimp only [M]
    convert ht using 1 <;> ring
  by_contra hn
  have hupper : z.re^2 ≤ 10/3 := le_of_not_gt hn
  have hneg := fourth_sextic_real_graph_negative (z.re^2) hX hupper
  have hnonneg : 0 ≤ β.re/z.re := div_nonneg hR hx.le
  have hyterm := mul_nonneg hα.le (sq_nonneg z.im)
  have hAM := mul_le_mul_of_nonneg_left hA hk.le
  rw [hRpart] at hnonneg
  rw [hM] at hAM
  dsimp only [α,b,k] at hnonneg hAM hyterm
  rw [show (z.re^2)^2=z.re^4 by ring] at hneg
  nlinarith only [hnonneg,hAM,hyterm,hneg]

end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(11/6)*w+(55/12)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-23/80+(33/640:ℂ)/(w^2-11/24)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) ∧
      (∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
        TeschlQM.Herglotz.borelTransform μ u) ∧
      ∃ z : ℂ,
        (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0 ∧
        w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.im ∧ 10/3 < z.re^2 ∧
        β/z = (((28-3*Real.sqrt 70)/55:ℝ):ℂ)*z^2-(((35-3*Real.sqrt 70)/50:ℝ):ℂ)+
          ((3*Real.sqrt 70/55:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by
  obtain ⟨z,hz,hr,hi⟩ := normalized_fourth_sextic_step β w hR hI.le hwpos hwim hwX hwroot hwinv
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hr
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hr]
  obtain ⟨μ,hfinite,hsupp,hμ⟩ := fourth_sextic_compact_positive_measure
  letI : IsFiniteMeasure μ := hfinite
  obtain ⟨hy0,hzero⟩ := fourth_sextic_nonnegative_im μ hsupp hμ β z hR hI.le hx hX hz
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  have hg := fourth_sextic_selected_graph μ hsupp hμ β w z hR hI.le hwpos hwim hwX hwinv hr hy hz
  have hloc := fourth_sextic_selected_localization μ hsupp hμ β z hR hx hy hX hg
  exact ⟨μ,hfinite,hsupp,hμ,z,hz,hr,hi,hy,hloc,hg⟩
