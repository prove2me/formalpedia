-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fourth_source_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T16:01:08.449343+00:00
-- url     : https://prove2.me/submissions/abd71815-5772-42d1-a49f-fb1f28134927

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

theorem iterated_derivative_real_parent (p : Polynomial ℂ) (k : ℕ)
    (hk : k < p.natDegree) (w : ℂ)
    (hw : (Polynomial.derivative^[k] p).eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by
  induction k generalizing p w with
  | zero => exact ⟨w, hw, le_rfl⟩
  | succ k ih =>
    have hkd : k < p.derivative.natDegree := by rw [Polynomial.natDegree_derivative]; omega
    rw [Function.iterate_succ_apply] at hw
    obtain ⟨u, hu, hwu⟩ := ih p.derivative hkd w hw
    obtain ⟨z, hz, huz⟩ := derivative_real_supporting_parent p (by omega) u hu
    exact ⟨z, hz, hwu.trans huz⟩

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
-- Source module: Rows


set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_fourth_power_expansion (β : ℂ) :
    ((X^3 - C (11/2) * X - 55 * C β)^4 : Polynomial ℂ) =
      C (1) * X^12 +
      C (-22) * X^10 +
      C (-220*β) * X^9 +
      C (363/2) * X^8 +
      C (3630*β) * X^7 +
      C (18150*β^2 - 1331/2) * X^6 +
      C (-19965*β) * X^5 +
      C (14641/16 - 199650*β^2) * X^4 +
      C (-665500*β^3 + 73205*β/2) * X^3 +
      C (1098075*β^2/2) * X^2 +
      C (3660250*β^3) * X^1 +
      C (9150625*β^4) * X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

theorem normalized_fourth_power_actual_rows (β z : ℂ) :
    let p : Polynomial ℂ := (X^3 - C (11/2) * X - 55 * C β)^4
    (derivative^[4] p).eval z = 11880 * (550*β^2*z^2 - 1210*β^2/3 - 56*β*z^5 + 770*β*z^3/3 - 605*β*z/3 + z^8 - 28*z^6/3 + 77*z^4/3 - 121*z^2/6 + 1331/720) ∧
    (derivative^[5] p).eval z = 95040 * (275*β^2*z/2 - 35*β*z^4 + 385*β*z^2/4 - 605*β/24 + z^7 - 7*z^5 + 77*z^3/6 - 121*z/24) ∧
    (derivative^[6] p).eval z = 665280 * (275*β^2/14 - 20*β*z^3 + 55*β*z/2 + z^6 - 5*z^4 + 11*z^2/2 - 121/168) ∧
    (derivative^[7] p).eval z = 3991680 * (-10*β*z^2 + 55*β/12 + z^5 - 10*z^3/3 + 11*z/6) ∧
    (derivative^[8] p).eval z = 19958400 * (-4*β*z + z^4 - 2*z^2 + 11/30) ∧
    (derivative^[9] p).eval z = 79833600 * (-β + z^3 - z) ∧
    (derivative^[10] p).eval z = 239500800 * (z^2 - 1/3) ∧
    (derivative^[11] p).eval z = 479001600 * (z) := by
  let p : Polynomial ℂ := (X^3 - C (11/2) * X - 55 * C β)^4
  have hexpand := normalized_fourth_power_expansion β
  change p = _ at hexpand
  dsimp only
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  all_goals change (derivative^[_] p).eval z = _
  all_goals rw [hexpand]
  all_goals simp only [iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  all_goals norm_num [Nat.descFactorial] <;> ring





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
-- Source module: OcticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators





















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

open DerivativeChainPrivate in
theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im) (hwX : 4 ≤ w.re^2)
    (hwroot : w^8-(28/3)*w^6-56*β*w^5+(77/3)*w^4+(770/3)*β*w^3-(121/6)*w^2+
      550*β^2*w^2-(605/3)*β*w+1331/720-(1210/3)*β^2=0)
    (hwinv : β/w = (((28-3*Real.sqrt 26)/550:ℝ):ℂ)*w^2-(((1274-99*Real.sqrt 26)/6500:ℝ):ℂ)+octicRemainder w/w) :
    ∃ z : ℂ, z^3-(11/2)*z-55*β=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im := by
  let q : Polynomial ℂ := X^3-C (11/2)*X-55*C β
  let p := q^4
  have hpdeg : p.natDegree=12 := by dsimp [p,q]; compute_degree <;> norm_num
  have hactual : (derivative^[4] p).eval w=0 := by
    have hh := (normalized_fourth_power_actual_rows β w).1
    change (derivative^[4] p).eval w = _ at hh
    rw [hh]
    linear_combination 11880*hwroot
  obtain ⟨z,hz,hxz⟩ := iterated_derivative_real_parent p 4 (by rw [hpdeg]; norm_num) w hactual
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hw0 : w ≠ 0 := by intro he; simp [he] at hwpos
  have hzq : q.eval z=0 := by
    have hh : (q.eval z)^4=0 := by simpa only [p,eval_pow] using hz
    exact (pow_eq_zero_iff (by norm_num : (4:ℕ) ≠ 0)).mp hh
  have hzroot : z^3-(11/2)*z-55*β=0 := by
    simpa only [q,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hzq
  have hzinv : β/z = (1/55:ℂ)*z^2-1/10+0/(z^2-0) := by
    simp only [zero_div,add_zero]
    apply (div_eq_iff hz0).mpr
    linear_combination (-1/55:ℂ)*hzroot
  obtain ⟨hzR,hzI,hzphase,_⟩ := rational_inverse_parts β z (1/55) (1/10) 0 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,zero_div,add_zero] at hzR hzI hzphase
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z (1/55) hR hI.le hx (by norm_num) hzphase
  have hy : 0 < z.im := by
    by_contra hn
    have hzIm : z.im=0 := le_antisymm (le_of_not_gt hn) hzim
    rw [hzIm,zero_mul] at hzI
    linarith
  let α := (28-3*Real.sqrt 26)/550
  let b := (1274-99*Real.sqrt 26)/6500
  obtain ⟨hwR,hwI,_⟩ := cubic_graph_coordinate_parts β w (octicRemainder w) α b hw0 hwinv
  have hC := (octic_remainder_coordinate_bounds w hwpos hwim hwX).2.2.2.2.2.1
  obtain ⟨_,_,_,hgap,hα,_,_,_,_,_⟩ := fourth_octic_scalar_gaps
  have himorder : w.im ≤ z.im := by
    by_contra hn
    apply inverse_graph_southeast_impossible α (1/55) b (1/10)
      ((octicRemainder w).re/w.re) 0 ((octicRemainder w).im/w.im) 0 (1/100)
      β.re β.im w.re w.im z.re z.im
      (by norm_num) hα hwpos hy hxz (le_of_not_ge hn) hR hI.le hC (by norm_num) hgap
    · rw [hwR]; field_simp <;> ring
    · rw [hwI]; field_simp <;> ring
    · rw [hzR]; field_simp <;> ring
    · rw [hzI]; field_simp <;> ring
  exact ⟨z,hzroot,hxz,himorder⟩
