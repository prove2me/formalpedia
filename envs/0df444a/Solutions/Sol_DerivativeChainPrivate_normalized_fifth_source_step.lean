-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_source_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T18:53:53.026678+00:00
-- url     : https://prove2.me/submissions/9f1698f5-4291-4d8c-82af-c74ae7d67d6a

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
-- Source module: FifthUnitRows

set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial
theorem fifth_unit_expansion (β : ℂ) : ((X^3-X-C β)^5 : Polynomial ℂ) =
    C ((1)*β^0)*X^15+
    C ((-5)*β^0)*X^13+
    C ((-5)*β^1)*X^12+
    C ((10)*β^0)*X^11+
    C ((20)*β^1)*X^10+
    C ((10)*β^2+(-10)*β^0)*X^9+
    C ((-30)*β^1)*X^8+
    C ((-30)*β^2+(5)*β^0)*X^7+
    C ((-10)*β^3+(20)*β^1)*X^6+
    C ((30)*β^2+(-1)*β^0)*X^5+
    C ((20)*β^3+(-5)*β^1)*X^4+
    C ((5)*β^4+(-10)*β^2)*X^3+
    C ((-10)*β^3)*X^2+
    C ((-5)*β^4)*X^1+
    C ((-1)*β^5)*X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

 

 




theorem fifth_unit_row_10 (β z : ℂ) :
    (derivative^[5] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z =
      360360*((1)*β^0*z^10+(-15/7)*β^0*z^8+(-120/91)*β^1*z^7+(20/13)*β^0*z^6+(240/143)*β^1*z^5+(60/143)*β^2*z^4+(-60/143)*β^0*z^4+(-80/143)*β^1*z^3+(-30/143)*β^2*z^2+(5/143)*β^0*z^2+(-20/1001)*β^3*z^1+(40/1001)*β^1*z^1+(10/1001)*β^2*z^0+(-1/3003)*β^0*z^0) := by
  rw [fifth_unit_expansion]
  simp only [iterate_map_add,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  norm_num [Nat.descFactorial] <;> ring
end DerivativeChainPrivate

end


section
-- Source module: FifthCubicRows

set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









theorem fifth_source_decic_row (β z : ℂ) :
    (derivative^[5] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z=360360*(fifthUnitP10 β).eval z := by
  rw [fifth_unit_row_10]
  norm_num [fifthUnitP10]
  ring
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β w e : ℂ) (α b : ℝ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 < w.im)
    (hwroot : (fifthUnitP10 β).eval w=0)
    (hαlo : 1461/1250 < α) (hblo : 2229/2000 < b)
    (hwinv : β/w=(α:ℂ)*w^2-(b:ℂ)+e/w)
    (hC : (3*(e.re/w.re)-e.im/w.im)/2 ≤ 3/50) :
    ∃ z : ℂ, z^3-z-β=0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im := by
  let q : Polynomial ℂ := X^3-X-C β
  let p := q^5
  have hpdeg : p.natDegree=15 := by dsimp [p,q]; compute_degree <;> norm_num
  have hactual : (derivative^[5] p).eval w=0 := by
    change (derivative^[5] ((X^3-X-C β)^5 : Polynomial ℂ)).eval w=0
    rw [fifth_source_decic_row,hwroot,mul_zero]
  obtain ⟨z,hz,hxz⟩ := iterated_derivative_real_parent p 5 (by rw [hpdeg]; norm_num) w hactual
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hz0 : z ≠ 0 := by intro he; simp [he] at hx
  have hw0 : w ≠ 0 := by intro he; simp [he] at hwpos
  have hzq : q.eval z=0 := by
    have hh : (q.eval z)^5=0 := by simpa only [p,eval_pow] using hz
    exact (pow_eq_zero_iff (by norm_num : (5:ℕ) ≠ 0)).mp hh
  have hzroot : z^3-z-β=0 := by
    simpa only [q,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hzq
  have hzinv : β/z = (1:ℂ)*z^2-1+0/(z^2-0) := by
    simp only [zero_div,add_zero]
    apply (div_eq_iff hz0).mpr
    linear_combination (-1:ℂ)*hzroot
  obtain ⟨hzR,hzI,hzphase,_⟩ := rational_inverse_parts β z (1) (1) 0 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,zero_div,add_zero] at hzR hzI hzphase
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z (1) hR hI.le hx (by norm_num) hzphase
  have hy : 0 < z.im := by
    by_contra hn
    have hzIm : z.im=0 := le_antisymm (le_of_not_gt hn) hzim
    rw [hzIm,zero_mul] at hzI
    linarith
  obtain ⟨hwR,hwI,_⟩ := cubic_graph_coordinate_parts β w e α b hw0 hwinv
  have hα : (1:ℝ) < α := by linarith only [hαlo]
  have hgap : (3/50:ℝ) < b-1 := by linarith only [hblo]
  have himorder : w.im ≤ z.im := by
    by_contra hn
    apply inverse_graph_southeast_impossible α (1) b (1)
      ((e).re/w.re) 0 ((e).im/w.im) 0 (3/50)
      β.re β.im w.re w.im z.re z.im
      (by norm_num) hα hwpos hy hxz (le_of_not_ge hn) hR hI.le hC (by norm_num) hgap
    · rw [hwR]; field_simp <;> ring
    · rw [hwI]; field_simp <;> ring
    · rw [hzR]; field_simp <;> ring
    · rw [hzI]; field_simp <;> ring
  exact ⟨z,hzroot,hxz,himorder⟩
