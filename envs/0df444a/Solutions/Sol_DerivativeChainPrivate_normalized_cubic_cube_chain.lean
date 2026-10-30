-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cubic_cube_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:18:57.627745+00:00
-- url     : https://prove2.me/submissions/b1a4238b-2aaf-4cd1-baa0-f2883eb6d57e

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_normalized_cube_actual_row_values
import Theorems.Thm_DerivativeChainPrivate_normalized_cube_quartic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_cube_quintic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_cube_sextic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_cube_source_step
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_positive_root_sector
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_quadrant_root
import Theorems.Thm_DerivativeChainPrivate_northeast_chain_cost
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

theorem power_root_inherited_derivative (q : Polynomial ℂ) (h k : ℕ)
    (z : ℂ) (hz : q.eval z = 0) (hk : k < h) :
    (Polynomial.derivative^[k] (q ^ h)).eval z = 0 := by
  obtain ⟨p, hp⟩ := Polynomial.pow_sub_dvd_iterate_derivative_pow q h k
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, hz,
    zero_pow (show h - k ≠ 0 by omega), zero_mul]



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
theorem solution (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 9 → ℂ,
      (∀ i, (derivative^[9-(i.val+1)] ((X^3-4*X-28*C β)^3)).eval (z i) = 0) ∧
      z 0 = 0 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧
      (z 8)^3-4*z 8-28*β = 0 ∧ 0 < (z 8).re ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2 * ‖z 8‖ := by
  obtain ⟨w₃,hw₃,_⟩ := normalized_cubic_quadrant_root β hR hI
  obtain ⟨hw₃re,hw₃im,_⟩ := normalized_cubic_positive_root_sector β w₃ hR hI hw₃.1 hw₃.2
  obtain ⟨w₄,hw₄,h₃₄r,h₃₄i,hw₄X,hw₄inv⟩ := normalized_cube_quartic_step β w₃ hR hI hw₃.1 hw₃.2
  have hw₄pos : 0 < w₄.re := lt_of_lt_of_le hw₃.2 h₃₄r
  obtain ⟨w₅,hw₅,h₄₅r,h₄₅i,hw₅X,hw₅inv⟩ := normalized_cube_quintic_step β w₄ hR hI
    hw₄pos (hw₃im.trans h₃₄i) hw₄X hw₄ hw₄inv
  have hw₅pos : 0 < w₅.re := lt_of_lt_of_le hw₄pos h₄₅r
  obtain ⟨w₆,hw₆,h₅₆r,h₅₆i,_,hw₆im,α,b,e,hα,hb,hw₆inv,hw₆zero,hw₆C⟩ :=
    normalized_cube_sextic_step β w₅ hR hI hw₅pos hw₅X hw₅ hw₅inv
  have hw₆pos : 0 < w₆.re := lt_of_lt_of_le hw₅pos h₅₆r
  obtain ⟨ρ,hρ,h₆ρr,h₆ρi,hρpos⟩ := normalized_cube_source_step β w₆ hR hI hw₆pos
    hw₆im hw₆ α b e hα hb hw₆inv hw₆zero hw₆C
  let c : ℝ := Real.sqrt 3 / 3
  have hcpos : 0 < c := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hc2 : c^2 = 1/3 := by
    dsimp only [c]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hc1 : c ≤ 1 := by nlinarith only [hc2,hcpos]
  have hcc : (c : ℂ)^2 = 1/3 := by
    rw [←Complex.ofReal_pow,hc2,Complex.ofReal_div]
    norm_num
  let g : ℕ → ℂ
    | 0 => 0
    | 1 => (c : ℂ)
    | 2 => w₃
    | 3 => w₄
    | 4 => w₅
    | 5 => w₆
    | _ => ρ
  have hre : ∀ i < 8, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> norm_num [g] <;>
      linarith only [hcpos,hc1,hw₃re,h₃₄r,h₄₅r,h₅₆r,h₆ρr]
  have him : ∀ i < 8, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> norm_num [g] <;>
      linarith only [hw₃im,h₃₄i,h₄₅i,h₅₆i,h₆ρi]
  have hqρ : (X^3-4*X-28*C β : Polynomial ℂ).eval ρ = 0 := by
    simpa only [eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hρ
  have hrows (i : ℕ) (hi : i < 9) :
      (derivative^[9-(i+1)] ((X^3-4*X-28*C β)^3)).eval (g i) = 0 := by
    interval_cases i
    · rw [(normalized_cube_actual_row_values β (g 0)).2.2.2.2.2]
      simp only [g,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 1)).2.2.2.2.1]
      simp only [g,hcc]
      norm_num
    · rw [(normalized_cube_actual_row_values β (g 2)).2.2.2.1]
      simp only [g,hw₃.1,sub_self,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 3)).2.2.1]
      simp only [g,hw₄,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 4)).2.1]
      simp only [g,hw₅,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 5)).1]
      simp only [g,hw₆,mul_zero]
    · exact power_root_inherited_derivative _ 3 2 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 3 1 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 3 0 ρ hqρ (by norm_num)
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,rfl,rfl,rfl,hρ,hρpos,?_,?_,?_⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
  · simpa only [g,sub_zero,Nat.reduceSub] using northeast_chain_cost 9 g hre him
