-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_prefix_five
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:40:27.379968+00:00
-- url     : https://prove2.me/submissions/e0b2190e-30c1-41e7-a399-030da47552c5

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_power_actual_rows
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


open DerivativeChainContinuation in
theorem solution (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(41/140)+(459/7840)/((z 4)^2-(17/42)) := by
  obtain ⟨w₃,hw₃,_⟩ := normalized_cubic_quadrant_root β hR hI
  obtain ⟨hw₃re,hw₃im,_⟩ := normalized_cubic_positive_root_sector β w₃ hR hI hw₃.1 hw₃.2
  obtain ⟨w₄,hw₄,h₃₄r,h₃₄i,hw₄X,hw₄inv⟩ :=
    normalized_quartic_step (17/48) (by norm_num) (by norm_num) β w₃ hR hI hw₃.1 hw₃.2
  have hw₄pos : 0 < w₄.re := lt_of_lt_of_le hw₃.2 h₃₄r
  obtain ⟨w₅,hw₅,h₄₅r,h₄₅i,hw₅X,hw₅inv⟩ :=
    normalized_quintic_step (17/48) (17/42) (41/140) (459/7840)
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
      (derivative^[18-(i+1)] ((X^3-C (17/2)*X-136*C β)^6)).eval (g i) = 0 := by
    interval_cases i
    · rw [(normalized_sixth_power_actual_rows β (g 0)).2.2.2.2.2.2.2.2.2.2.2]
      simp only [g,mul_zero]
    · rw [(normalized_sixth_power_actual_rows β (g 1)).2.2.2.2.2.2.2.2.2.2.1]
      simp only [g,hrc]
      norm_num
    · rw [(normalized_sixth_power_actual_rows β (g 2)).2.2.2.2.2.2.2.2.2.1]
      simp only [g]
      linear_combination 1067062284288000 * hw₃.1
    · rw [(normalized_sixth_power_actual_rows β (g 3)).2.2.2.2.2.2.2.2.1]
      simp only [g]
      linear_combination 266765571072000 * hw₄
    · rw [(normalized_sixth_power_actual_rows β (g 4)).2.2.2.2.2.2.2.1]
      simp only [g]
      linear_combination 53353114214400 * hw₅
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,rfl,?_,?_,hw₅pos,hw₅X,hw₅inv⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
