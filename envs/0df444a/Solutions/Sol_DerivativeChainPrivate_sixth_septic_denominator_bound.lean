-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:03:03.404753+00:00
-- url     : https://prove2.me/submissions/7266555f-0ef1-4c7d-bf24-f13d7c9318d6

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_foundations
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


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators








theorem sixth_septic_poly_bound (u : ℂ) (hu : ‖u‖≤3/8) :
    ‖sixthSepticPoly u-1‖≤4/5 := by
  have hs:=norm_real_power_sum_le sixthSepticCoeffs u (3/8) (by norm_num) hu
  calc
    _=‖u‖*‖∑ i : Fin 20,(sixthSepticCoeffs i:ℂ)*u^i.val‖ := by simp [sixthSepticPoly,norm_mul]
    _≤(3/8)*(∑ i : Fin 20,|sixthSepticCoeffs i| *(3/8:ℝ)^i.val) :=
      mul_le_mul hu hs (norm_nonneg _) (by norm_num)
    _≤4/5 := by norm_num [sixthSepticCoeffs,Fin.sum_univ_succ]


end DerivativeChainPrivate

theorem solution (u : ℂ) (hu : ‖u‖≤3/8) :
    Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u≠0 ∧
      ‖(Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u)⁻¹‖≤5 := by
  have hs : 0≤(Complex.sqrt (sixthSepticRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp:=sixth_septic_poly_bound u hu
  have hr:=Complex.re_le_norm (1-sixthSepticPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re,Complex.one_re] at hr
  have hd:=Complex.re_le_norm (Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/5:ℝ)≤‖Complex.sqrt (sixthSepticRadicand u)+sixthSepticPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi:=inv_anti₀ (by norm_num : (0:ℝ)<1/5) hl
  norm_num at hi
  exact hi
