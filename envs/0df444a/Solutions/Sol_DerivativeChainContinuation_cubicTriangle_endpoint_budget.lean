-- Prove2me | solution 1 for DerivativeChainContinuation.cubicTriangle_endpoint_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:23:11.737955+00:00
-- url     : https://prove2.me/submissions/22014458-4208-4e0e-9007-db54bd5e87c1

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicCertificate
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainContinuation_SharpCubicTriangle
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_cubicTriangle_acute_radius
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
namespace DerivativeChainContinuation



theorem sharpCubicConstant_positive : 0 < sharpCubicConstant := by
  unfold sharpCubicConstant
  positivity

theorem sharpCubicConstant_equation :
    3*sharpCubicConstant^2-2*sharpCubicConstant-3=0 := by
  unfold sharpCubicConstant
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  nlinarith

theorem sharpCubicConstant_gt_four_thirds : (4/3 : ℝ) < sharpCubicConstant := by
  unfold sharpCubicConstant
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hp := Real.sqrt_nonneg 10
  nlinarith



theorem sharpCubic_one_variable_bound (s : ℝ) :
    2*s*(3+s) ≤ 3*sharpCubicConstant*(1+s^2) := by
  have he := sharpCubicConstant_equation
  have hp := sharpCubicConstant_positive
  have hid : sharpCubicConstant*(3*sharpCubicConstant*(1+s^2)-2*s*(3+s)) =
      3*(s-sharpCubicConstant)^2 := by
    linear_combination s^2*he
  have hn := sq_nonneg (s-sharpCubicConstant)
  have hh : 0 ≤ sharpCubicConstant*(3*sharpCubicConstant*(1+s^2)-2*s*(3+s)) := by
    rw [hid]; positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hh)

end DerivativeChainContinuation


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainContinuation







theorem sharpCubicCertificate_identity (k s : ℝ) :
    (3+s)^2*(16*cubicSideU k s*cubicSideV k s*cubicSideW k s) -
      4*(3+k*s)^2*(k^2+3)^2*(1+s^2)^2 = sharpCubicCertificate k (s-1) := by
  unfold cubicSideU cubicSideV cubicSideW sharpCubicCertificate
  ring

theorem sharpCubicCertificate_nonneg (k s : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hs : 1 ≤ s) : 0 ≤ sharpCubicCertificate k (s-1) := by
  have hkc : 0 ≤ 1-k := sub_nonneg.mpr hk1
  have hsc : 0 ≤ s-1 := sub_nonneg.mpr hs
  unfold sharpCubicCertificate
  positivity

theorem sharpCubic_comparison (k s : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hs : 1 ≤ s) :
    4*(3+k*s)^2*(k^2+3)^2*(1+s^2)^2 ≤
      (3+s)^2*(16*cubicSideU k s*cubicSideV k s*cubicSideW k s) := by
  have h := sharpCubicCertificate_nonneg k s hk hk1 hs
  rw [← sharpCubicCertificate_identity] at h
  linarith

end DerivativeChainContinuation


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation





theorem cubicTriangle_sides (k s : ℝ) :
    Complex.normSq (cubicTriangleA k s-cubicTriangleB k s)=cubicSideU k s ∧
    Complex.normSq (cubicTriangleA k s-cubicTriangleC k s)=cubicSideV k s ∧
    Complex.normSq (cubicTriangleB k s-cubicTriangleC k s)=cubicSideW k s := by
  simp only [cubicTriangleA,cubicTriangleB,cubicTriangleC,cubicSideU,cubicSideV,cubicSideW,
    Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  constructor
  · ring
  constructor <;> ring



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (k s : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hs0 : 0 ≤ s) (hs3 : s^2 ≤ 3) (o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ‖cubicTriangleA k s-o‖ ≤ R) (hb : ‖cubicTriangleB k s-o‖ ≤ R)
    (hc : ‖cubicTriangleC k s-o‖ ≤ R) :
    1+k*s/3 ≤ sharpCubicConstant*R := by
  have hcpos := sharpCubicConstant_positive
  by_cases hs1 : s ≤ 1
  · have hd : ‖cubicTriangleA k s-cubicTriangleC k s‖ ≤ 2*R := by
      have h := norm_sub_le (cubicTriangleA k s-o) (cubicTriangleC k s-o)
      simp only [sub_sub_sub_cancel_right] at h
      linarith
    have hv := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*R)).mpr hd
    rw [← Complex.normSq_eq_norm_sq, (cubicTriangle_sides k s).2.1] at hv
    have hid : 4*cubicSideV k s-(3+k*s)^2 = (k-s)^2+2*k*(1-s)*(3+s) := by
      unfold cubicSideV; ring
    have hp : 0 ≤ 2*k*(1-s)*(3+s) := by positivity
    have ht : 3+k*s ≤ 4*R := by nlinarith [sq_nonneg (k-s), mul_nonneg hk hs0]
    have hh := mul_le_mul_of_nonneg_right sharpCubicConstant_gt_four_thirds.le hR
    nlinarith
  · have hs : 1 ≤ s := le_of_lt (lt_of_not_ge hs1)
    have hspos : 0 < s := by linarith
    have hg := cubicTriangle_acute_radius k s hk hk1 hs hs3 o R hR ha hb hc
    have hcert := sharpCubic_comparison k s hk hk1 hs
    have hm := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 16*(3+s)^2)
    have hd : 0 < (k^2+3)^2 := by positivity
    have hprod : (k^2+3)^2*(4*(3+k*s)^2*(1+s^2)^2) ≤
        (k^2+3)^2*(16*(3+s)^2*s^2*R^2) := by nlinarith
    have hcancel := (mul_le_mul_iff_right₀ hd).mp hprod
    have hsq : ((3+k*s)*(1+s^2))^2 ≤ (2*s*(3+s)*R)^2 := by nlinarith
    have hlin := (sq_le_sq₀ (by positivity : 0 ≤ (3+k*s)*(1+s^2))
      (by positivity : 0 ≤ 2*s*(3+s)*R)).mp hsq
    have hmax := mul_le_mul_of_nonneg_right (sharpCubic_one_variable_bound s) hR
    have hcros : (1+s^2)*(3+k*s) ≤ (1+s^2)*(3*sharpCubicConstant*R) := by nlinarith
    have hlast := (mul_le_mul_iff_right₀ (by positivity : 0 < 1+s^2)).mp hcros
    nlinarith
