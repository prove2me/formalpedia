-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fourth_prefix_five
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:25:11.548366+00:00
-- url     : https://prove2.me/submissions/98409184-f40a-4d5d-adc2-ac8f01a3f730

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_positive_root_sector
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_quadrant_root
import Theorems.Thm_DerivativeChainPrivate_normalized_quartic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_quintic_step
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000



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

open DerivativeChainPrivate in
theorem solution (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[12-(i.val+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(23/80)+(33/640)/((z 4)^2-(11/24)) := by
  obtain ⟨w₃,hw₃,_⟩ := normalized_cubic_quadrant_root β hR hI
  obtain ⟨hw₃re,hw₃im,_⟩ := normalized_cubic_positive_root_sector β w₃ hR hI hw₃.1 hw₃.2
  obtain ⟨w₄,hw₄,h₃₄r,h₃₄i,hw₄X,hw₄inv⟩ :=
    normalized_quartic_step (11/30) (by norm_num) (by norm_num) β w₃ hR hI hw₃.1 hw₃.2
  have hw₄pos : 0 < w₄.re := lt_of_lt_of_le hw₃.2 h₃₄r
  obtain ⟨w₅,hw₅,h₄₅r,h₄₅i,hw₅X,hw₅inv⟩ :=
    normalized_quintic_step (11/30) (11/24) (23/80) (33/640)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      β w₄ hR hI hw₄pos (hw₃im.trans h₃₄i) hw₄X hw₄ hw₄inv
  norm_num at hw₄ hw₄inv hw₅ hw₅inv
  have hw₅pos : 0 < w₅.re := lt_of_lt_of_le hw₄pos h₄₅r
  let r : ℝ := Real.sqrt 3 / 3
  have hrpos : 0 < r := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hr2 : r^2 = 1/3 := by
    dsimp only [r]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hr1 : r ≤ 1 := by nlinarith only [hr2,hrpos]
  have hrc : (r : ℂ)^2 = 1/3 := by
    rw [←Complex.ofReal_pow,hr2,Complex.ofReal_div]
    norm_num
  let g : ℕ → ℂ
    | 0 => 0
    | 1 => (r : ℂ)
    | 2 => w₃
    | 3 => w₄
    | _ => w₅
  have hre : ∀ i < 4, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> norm_num [g] <;> linarith only [hrpos,hr1,hw₃re,h₃₄r,h₄₅r]
  have him : ∀ i < 4, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> norm_num [g] <;> linarith only [hw₃im,h₃₄i,h₄₅i]
  have hrows (i : ℕ) (hi : i < 5) :
      (derivative^[12-(i+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (g i) = 0 := by
    interval_cases i
    · rw [(normalized_fourth_power_actual_rows β (g 0)).2.2.2.2.2.2.2]
      simp only [g,mul_zero]
    · rw [(normalized_fourth_power_actual_rows β (g 1)).2.2.2.2.2.2.1]
      simp only [g,hrc]
      norm_num
    · rw [(normalized_fourth_power_actual_rows β (g 2)).2.2.2.2.2.1]
      simp only [g]
      linear_combination 79833600 * hw₃.1
    · rw [(normalized_fourth_power_actual_rows β (g 3)).2.2.2.2.1]
      simp only [g]
      linear_combination 19958400 * hw₄
    · rw [(normalized_fourth_power_actual_rows β (g 4)).2.2.2.1]
      simp only [g]
      linear_combination 3991680 * hw₅
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,rfl,?_,?_,hw₅pos,hw₅X,hw₅inv⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
