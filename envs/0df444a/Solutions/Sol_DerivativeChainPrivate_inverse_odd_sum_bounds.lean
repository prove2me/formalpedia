-- Prove2me | solution 1 for DerivativeChainPrivate.inverse_odd_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:40:13.441295+00:00
-- url     : https://prove2.me/submissions/9028f1f8-65eb-4dbe-8801-61edea016e90

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_inverse_power_coordinate_bounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DerivativeChainPrivate
open scoped BigOperators



theorem inverse_power_correction_bound (q : ℕ) (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) :
    |(3*(((z⁻¹)^(q+1)).re/z.re)-((z⁻¹)^(q+1)).im/z.im)/2|≤
      ((q+4:ℝ)/2)*(z.re⁻¹)^(q+2) := by
  obtain ⟨hR,hI⟩:=inverse_power_coordinate_bounds q z hx hy
  rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have ht:=norm_sub_le (3*(((z⁻¹)^(q+1)).re/z.re)) (((z⁻¹)^(q+1)).im/z.im)
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤3)] at ht
  calc
    _≤3*|((z⁻¹)^(q+1)).re/z.re|+|((z⁻¹)^(q+1)).im/z.im| := ht
    _≤3*(z.re⁻¹)^(q+2)+(q+1:ℝ)*(z.re⁻¹)^(q+2) :=
      add_le_add (mul_le_mul_of_nonneg_left hR (by norm_num)) hI
    _=((q+4:ℝ)/2)*(z.re⁻¹)^(q+2)*2 := by ring

theorem inverse_odd_power_bounds (k : ℕ) (T : ℝ) (hT : 0<T) (z : ℂ)
    (hx : 0<z.re) (hy : 0<z.im) (hX : T≤z.re^2) :
    |((z⁻¹)^(2*k+1)).re/z.re|≤(T⁻¹)^(k+1) ∧
      |(3*(((z⁻¹)^(2*k+1)).re/z.re)-((z⁻¹)^(2*k+1)).im/z.im)/2|≤
        (k+2:ℝ)*(T⁻¹)^(k+1) := by
  have hi : (z.re⁻¹)^2≤T⁻¹ := by rw [inv_pow]; exact inv_anti₀ hT hX
  have hp : (z.re⁻¹)^(2*k+2)≤(T⁻¹)^(k+1) := by
    rw [show 2*k+2=2*(k+1) by omega,pow_mul]
    gcongr
  have hR:=(inverse_power_coordinate_bounds (2*k) z hx hy).1
  have hC:=inverse_power_correction_bound (2*k) z hx hy
  push_cast at hC
  have he : (2*(k:ℝ)+4)/2=(k:ℝ)+2 := by ring
  rw [he] at hC
  exact ⟨hR.trans hp,hC.trans (mul_le_mul_of_nonneg_left hp (by positivity))⟩





end DerivativeChainPrivate

theorem solution {n : ℕ} (c : Fin n → ℝ) (k : Fin n → ℕ)
    (T : ℝ) (hT : 0<T) (z : ℂ) (hx : 0<z.re) (hy : 0<z.im) (hX : T≤z.re^2) :
    let E:=∑ i,(c i:ℂ)*(z⁻¹)^(2*k i+1)
    |E.re/z.re|≤∑ i,|c i| *(T⁻¹)^(k i+1) ∧
      |(3*(E.re/z.re)-E.im/z.im)/2|≤∑ i,|c i| *(k i+2:ℝ)*(T⁻¹)^(k i+1) := by
  dsimp only
  have hR : (∑ i,(c i:ℂ)*(z⁻¹)^(2*k i+1)).re/z.re=
      ∑ i,c i*(((z⁻¹)^(2*k i+1)).re/z.re) := by
    simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hI : (∑ i,(c i:ℂ)*(z⁻¹)^(2*k i+1)).im/z.im=
      ∑ i,c i*(((z⁻¹)^(2*k i+1)).im/z.im) := by
    simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hC : (3*((∑ i,(c i:ℂ)*(z⁻¹)^(2*k i+1)).re/z.re)-
      (∑ i,(c i:ℂ)*(z⁻¹)^(2*k i+1)).im/z.im)/2=
      ∑ i,c i*((3*(((z⁻¹)^(2*k i+1)).re/z.re)-((z⁻¹)^(2*k i+1)).im/z.im)/2) := by
    rw [hR,hI,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · rw [hR]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (inverse_odd_power_bounds (k i) T hT z hx hy hX).1 (abs_nonneg _)
  · rw [hC]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (inverse_odd_power_bounds (k i) T hT z hx hy hX).2 (abs_nonneg (c i))
