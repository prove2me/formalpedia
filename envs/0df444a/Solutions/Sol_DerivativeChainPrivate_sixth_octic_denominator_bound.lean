-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:21:47.390483+00:00
-- url     : https://prove2.me/submissions/c82702cb-974e-4776-bdb6-102ac776f8fc

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
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
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators















theorem sixth_octic_sqrt_rest_identity (u : ℂ) :
    sixthOcticPoly u-(1-(1105/363)*u+(293335/175692)*u^2)=
      u^3*(∑ i : Fin 18,(sixthOcticSqrtRestCoeffs i:ℂ)*u^i.val) := by
  norm_num [sixthOcticPoly,sixthOcticCoeffs,sixthOcticSqrtRestCoeffs,Fin.sum_univ_succ]
  ring

theorem sixth_octic_sqrt_rest_bound (u : ℂ) (hu : ‖u‖≤3/10) :
    ‖sixthOcticPoly u-(1-(1105/363)*u+(293335/175692)*u^2)‖≤1/100 := by
  rw [sixth_octic_sqrt_rest_identity,norm_mul,norm_pow]
  have hs:=norm_real_power_sum_le sixthOcticSqrtRestCoeffs u (3/10) (by norm_num) hu
  calc
    _≤(3/10)^3*(∑ i : Fin 18,|sixthOcticSqrtRestCoeffs i| *(3/10:ℝ)^i.val) := by gcongr
    _≤1/100 := by norm_num [sixthOcticSqrtRestCoeffs,sixthOcticCoeffs,Fin.sum_univ_succ]




end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace DerivativeChainPrivate







theorem sixth_octic_poly_real_lower (u : ℂ) (hu : ‖u‖≤3/10) : (1/5:ℝ)≤(sixthOcticPoly u).re := by
  let x:=u.re
  let Y:=u.im^2
  let V:=(3/10:ℝ)^2-x^2
  let P₂ : ℂ:=1-(1105/363)*u+(293335/175692)*u^2
  have hx : x≤3/10 := le_trans (Complex.re_le_norm u) hu
  have hyV : Y≤V := by
    have hn:=Complex.sq_norm u
    simp only [Complex.normSq_apply] at hn
    dsimp [Y,V,x]
    nlinarith [norm_nonneg u]
  have hf : 0≤(1105/363:ℝ)-2*(293335/175692)*(x+3/10) := by linarith
  have hp:=mul_nonneg (show 0≤3/10-x by linarith) hf
  have hP₂ : (23/100:ℝ)≤P₂.re := by
    have he : P₂.re=1-(1105/363)*x+(293335/175692)*(x^2-Y) := by
      dsimp [P₂,x,Y]
      norm_num [pow_two,Complex.mul_re,Complex.mul_im] <;> ring
    rw [he]
    dsimp [V] at hyV
    nlinarith
  have hrest:=sixth_octic_sqrt_rest_bound u hu
  change ‖sixthOcticPoly u-P₂‖≤1/100 at hrest
  have hr:=Complex.re_le_norm (P₂-sixthOcticPoly u)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re] at hr
  linarith




end DerivativeChainPrivate

theorem solution (u : ℂ) (hu : ‖u‖≤3/10) :
    Complex.sqrt (sixthOcticRadicand u)+sixthOcticPoly u≠0 ∧
      ‖(Complex.sqrt (sixthOcticRadicand u)+sixthOcticPoly u)⁻¹‖≤5 := by
  have hs : 0≤(Complex.sqrt (sixthOcticRadicand u)).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hp:=sixth_octic_poly_real_lower u hu
  have hd:=Complex.re_le_norm (Complex.sqrt (sixthOcticRadicand u)+sixthOcticPoly u)
  simp only [Complex.add_re] at hd
  have hl : (1/5:ℝ)≤‖Complex.sqrt (sixthOcticRadicand u)+sixthOcticPoly u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi:=inv_anti₀ (by norm_num : (0:ℝ)<1/5) hl
  norm_num at hi
  exact hi
