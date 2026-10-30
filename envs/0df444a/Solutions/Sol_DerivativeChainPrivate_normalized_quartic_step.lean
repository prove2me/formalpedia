-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_quartic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:34:37.519672+00:00
-- url     : https://prove2.me/submissions/8e68bf13-562e-4f88-b8de-827b2c2bfd5f

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_derivative_real_supporting_parent
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_positive_root_sector
import Theorems.Thm_DerivativeChainPrivate_quadrant_phase_forces_nonnegative_im
import Theorems.Thm_DerivativeChainPrivate_rational_inverse_parts
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


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



open DerivativeChainPrivate in
theorem solution (c : ℝ) (hc : 0 ≤ c) (hcUpper : c ≤ 8/21) (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hw : w ^ 3 - w = β) (hwpos : 0 < w.re) :
    ∃ z : ℂ,
      z ^ 4 - 2 * z ^ 2 - 4 * β * z + c = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7 / 4 ≤ z.re ^ 2 ∧
      β / z = (1/4 : ℂ) * z ^ 2 - 1/2 + (c/4 : ℂ) / z ^ 2 := by
  obtain ⟨hw1,hwim,hwsector⟩ := normalized_cubic_positive_root_sector β w hR hI hw hwpos
  have hwne : w ≠ 0 := by intro h; simp [h] at hwpos
  have hwinv : β / w = (1 : ℂ) * w ^ 2 - 1 + 0 / (w ^ 2 - 0) := by
    rw [← hw]
    field_simp
    ring
  obtain ⟨hwR,hwI,hwphase,_⟩ := rational_inverse_parts β w 1 1 0 0 hwne
    (by simpa using pow_ne_zero 2 hwne) hwinv
  simp only [zero_mul,zero_div,sub_zero,add_zero,one_mul] at hwR hwI hwphase
  have hwzero := (quadrant_phase_forces_nonnegative_im β w 1 hR hI hwpos
    (by norm_num) (by simpa only [mul_one] using hwphase)).2
  let p : Polynomial ℂ := X ^ 4 - 2 * X ^ 2 - 4 * C β * X + C (c : ℂ)
  have hpdeg : p.natDegree = 4 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 4 * hw
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx1 : 1 ≤ z.re := hw1.trans hxz
  have hx : 0 < z.re := by linarith
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hzroot : z ^ 4 - 2 * z ^ 2 - 4 * β * z + c = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  have hzinv : β / z = (1 / 4 : ℂ) * z ^ 2 - 1 / 2 + (c/4 : ℂ) / (z ^ 2 - 0) := by
    have hform : β / z = (z ^ 4 - 2 * z ^ 2 + c) / (4 * z ^ 2) := by
      apply (div_eq_div_iff hz0 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))).2
      linear_combination (-z) * hzroot
    rw [hform]
    field_simp
    ring
  obtain ⟨hzR,hzI,hzphase,hD⟩ := rational_inverse_parts β z (1/4) (1/2) (c/4) 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,add_zero] at hzR hzI hzphase hD
  let U := z.re ^ 2 + z.im ^ 2
  have hU : 1 ≤ U := by dsimp only [U]; nlinarith only [hx1,sq_nonneg z.im]
  have hUpos : 0 < U := by linarith
  have hDpos : 0 < ‖z ^ 2‖ ^ 2 := by rw [hD]; change 0 < U ^ 2; positivity
  have hD1 : 1 ≤ ‖z ^ 2‖ ^ 2 := by rw [hD]; change 1 ≤ U ^ 2; nlinarith only [hU]
  have hphasepos : 0 < (1/4 : ℝ) - (c/4) / ‖z ^ 2‖ ^ 2 := by
    have hquot : (c/4 : ℝ) / ‖z ^ 2‖ ^ 2 ≤ c/4 :=
      by simpa using div_le_div_of_nonneg_left (show (0 : ℝ) ≤ c/4 by positivity) (by norm_num : (0 : ℝ) < 1) hD1
    linarith
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z _ hR hI hx hphasepos hzphase
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzero : z.im = 0
    · have hβzero : β.im = 0 := by rw [hzI,hzero,zero_mul]
      have hwzero' := hwzero hβzero
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzero)
      have hy : 0 < w.im := lt_trans hv hlt
      apply inverse_graph_southeast_impossible 1 (1/4) 1 (1/2) 0
        ((c/4) * U / ‖z ^ 2‖ ^ 2) 0 (-((c/4) * U / ‖z ^ 2‖ ^ 2)) 0
        β.re β.im w.re w.im z.re z.im
        (by norm_num) (by norm_num) hwpos hv hxz hlt.le hR hI
        (by norm_num) (by
          have hA : 0 ≤ (c/4 : ℝ) * U / ‖z ^ 2‖ ^ 2 := by positivity
          linarith only [hA]) (by norm_num)
      · rw [hwR]; field_simp <;> ring
      · rw [hwI]; field_simp <;> ring
      · rw [hzR]; dsimp only [U]; field_simp <;> ring
      · rw [hzI]; dsimp only [U]; field_simp <;> ring
  have hXpos : 0 < z.re ^ 2 := sq_pos_of_pos hx
  have hbr : 0 ≤ (1/4 : ℝ) * (z.re ^ 2 - 3 * z.im ^ 2) - 1/2 +
      (c/4) * U / ‖z ^ 2‖ ^ 2 := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [U] using (hzR ▸ hR)
  have hrewrite : (c/4 : ℝ) * U / ‖z ^ 2‖ ^ 2 = (c/4) / U := by
    rw [hD]; change (c/4 : ℝ) * U / U ^ 2 = (c/4) / U
    field_simp
  rw [hrewrite] at hbr
  have hquot := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ c/4 by positivity) hXpos
    (show z.re ^ 2 ≤ U by dsimp only [U]; nlinarith only [sq_nonneg z.im])
  have hweak : 0 ≤ z.re ^ 2 / 4 - 1/2 + (c/4) / z.re ^ 2 := by
    nlinarith only [hbr,hquot,sq_nonneg z.im]
  have hid : z.re ^ 2 / 4 - 1/2 + (c/4) / z.re ^ 2 =
      ((z.re ^ 2) ^ 2 - 2 * z.re ^ 2 + c) / (4 * z.re ^ 2) := by field_simp; ring
  rw [hid] at hweak
  have hpoly := (le_div_iff₀ (show 0 < 4 * z.re ^ 2 by positivity)).mp hweak
  have hX1 : 1 ≤ z.re ^ 2 := by nlinarith only [hx1]
  have hX : 7/4 ≤ z.re ^ 2 := by
    by_contra hfail
    have hprod := mul_nonneg (show 0 ≤ z.re ^ 2 - 1 by linarith)
      (show 0 ≤ 7/4 - z.re ^ 2 by linarith)
    nlinarith only [hpoly,hprod,lt_of_not_ge hfail,hcUpper]
  exact ⟨z,hzroot,hxz,himorder,hX,by simpa only [sub_zero] using hzinv⟩
