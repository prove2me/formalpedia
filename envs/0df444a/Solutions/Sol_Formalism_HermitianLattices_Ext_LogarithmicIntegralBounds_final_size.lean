-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.final_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:33.456533+00:00
-- url     : https://prove2.me/submissions/ae908530-3643-4849-869e-7405c5ce80b6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (ε : ℝ) (hε1 : ε ≤ 1) (x : ℝ) (hx3 : 3 ≤ x) (C1 C2 C3 C4 S1 Sd R : ℝ)
    (hS0 : 0 ≤ S1) (hS1 : S1 ≤ C1 * x * Real.log x) (hSd : Sd ≤ C4 * x * Real.log x) (hR0 : 0 ≤ R)
    (hR : R ≤ C3 * (Real.sqrt x + x ^ (ε / 5) * Real.log x)) :
    Sd + R ^ 2 + (2 * (|C2| * Real.log x) ^ 2 + 2 * (|C2| * Real.log x) * R) + x ^ (-3 : ℝ) * S1 ^ 2 ≤
      (|C4| + 25 * C3 ^ 2 + 2 * C2 ^ 2 + 10 * |C2| * |C3| + C1 ^ 2) * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ Real.log x := by linarith
  have hLx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hsq : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · rw [sq]
      exact le_mul_of_one_le_right hx0.le hx1
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have ha0 : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have hab : x ^ (ε / 5) ≤ x ^ (1 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hL45 : Real.log x ≤ x ^ (4 / 5 : ℝ) / (4 / 5) := Real.log_le_rpow_div hx0.le (by norm_num)
  have hL35 : Real.log x ≤ x ^ (3 / 5 : ℝ) / (3 / 5) := Real.log_le_rpow_div hx0.le (by norm_num)
  have hp45 : x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hp35 : (x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ) = x := by
    rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]; norm_num
  have hb0 : 0 ≤ x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have hc45 : 0 ≤ x ^ (4 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have hc35 : 0 ≤ x ^ (3 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have haL : x ^ (ε / 5) * Real.log x ≤ 5 / 4 * x := by
    calc x ^ (ε / 5) * Real.log x ≤ x ^ (1 / 5 : ℝ) * (x ^ (4 / 5 : ℝ) / (4 / 5)) :=
          mul_le_mul hab hL45 hL0 hb0
      _ = 5 / 4 * (x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ)) := by ring
      _ = 5 / 4 * x := by rw [hp45]
  have haL2 : (x ^ (ε / 5) * Real.log x) ^ 2 ≤ 5 / 3 * x * Real.log x := by
    have h1 : (x ^ (ε / 5)) ^ 2 ≤ (x ^ (1 / 5 : ℝ)) ^ 2 := pow_le_pow_left₀ ha0 hab 2
    calc (x ^ (ε / 5) * Real.log x) ^ 2 = (x ^ (ε / 5)) ^ 2 * Real.log x * Real.log x := by ring
      _ ≤ (x ^ (1 / 5 : ℝ)) ^ 2 * (x ^ (3 / 5 : ℝ) / (3 / 5)) * Real.log x := by
          apply mul_le_mul_of_nonneg_right _ hL0
          exact mul_le_mul h1 hL35 hL0 (sq_nonneg _)
      _ = 5 / 3 * ((x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ)) * Real.log x := by ring
      _ = 5 / 3 * x * Real.log x := by rw [hp35]
  set T := Real.sqrt x + x ^ (ε / 5) * Real.log x with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hT : T ≤ 9 / 4 * x := by linarith
  have hT2 : T ^ 2 ≤ 16 / 3 * x * Real.log x := by
    have e : T ^ 2 = 2 * Real.sqrt x ^ 2 + 2 * (x ^ (ε / 5) * Real.log x) ^ 2 -
        (Real.sqrt x - x ^ (ε / 5) * Real.log x) ^ 2 := by rw [hTdef]; ring
    have hxL1 : x ≤ x * Real.log x := le_mul_of_one_le_right hx0.le hL1
    have hs := sq_nonneg (Real.sqrt x - x ^ (ε / 5) * Real.log x)
    rw [e, hsx]
    linarith
  have hC3T : 0 ≤ C3 * T := hR0.trans hR
  have hR2 : R ^ 2 ≤ C3 ^ 2 * (16 / 3 * x * Real.log x) := by
    calc R ^ 2 ≤ (C3 * T) ^ 2 := pow_le_pow_left₀ hR0 hR 2
      _ = C3 ^ 2 * T ^ 2 := by ring
      _ ≤ C3 ^ 2 * (16 / 3 * x * Real.log x) := mul_le_mul_of_nonneg_left hT2 (sq_nonneg _)
  have hRT : R ≤ |C3| * T := hR.trans (mul_le_mul_of_nonneg_right (le_abs_self C3) hT0)
  have hxL : 0 ≤ x * Real.log x := mul_nonneg hx0.le hL0
  have e1 : Sd ≤ |C4| * x * Real.log x := by
    calc Sd ≤ C4 * x * Real.log x := hSd
      _ = C4 * (x * Real.log x) := by ring
      _ ≤ |C4| * (x * Real.log x) := mul_le_mul_of_nonneg_right (le_abs_self C4) hxL
      _ = |C4| * x * Real.log x := by ring
  have hC2 : 0 ≤ |C2| := abs_nonneg C2
  have hC3 : 0 ≤ |C3| := abs_nonneg C3
  have e3 : 2 * (|C2| * Real.log x) * R ≤ 9 / 2 * (|C2| * |C3|) * (x * Real.log x) := by
    have h1 : 0 ≤ 2 * (|C2| * Real.log x) := by positivity
    calc 2 * (|C2| * Real.log x) * R ≤ 2 * (|C2| * Real.log x) * (|C3| * T) :=
          mul_le_mul_of_nonneg_left hRT h1
      _ ≤ 2 * (|C2| * Real.log x) * (|C3| * (9 / 4 * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hC3) h1
      _ = 9 / 2 * (|C2| * |C3|) * (x * Real.log x) := by ring
  have e4 : 2 * (|C2| * Real.log x) ^ 2 ≤ 2 * C2 ^ 2 * (x * Real.log x) := by
    have : (|C2| * Real.log x) ^ 2 = C2 ^ 2 * (Real.log x * Real.log x) := by rw [mul_pow, sq_abs]; ring
    rw [this]
    have h2 : Real.log x * Real.log x ≤ x * Real.log x := mul_le_mul_of_nonneg_right hLx hL0
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C2)
    linarith
  have e5 : x ^ (-3 : ℝ) * S1 ^ 2 ≤ C1 ^ 2 * (x * Real.log x) := by
    have hS2 : S1 ^ 2 ≤ (C1 * x * Real.log x) ^ 2 := pow_le_pow_left₀ hS0 hS1 2
    have hx3 : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
      rw [Real.rpow_neg hx0.le]; norm_cast
    rw [hx3]
    have hx30 : 0 < x ^ 3 := by positivity
    calc (x ^ 3)⁻¹ * S1 ^ 2 ≤ (x ^ 3)⁻¹ * (C1 * x * Real.log x) ^ 2 :=
          mul_le_mul_of_nonneg_left hS2 (inv_nonneg.mpr hx30.le)
      _ = C1 ^ 2 * (Real.log x * Real.log x) / x := by field_simp
      _ ≤ C1 ^ 2 * (x * Real.log x) := by
          rw [div_le_iff₀ hx0]
          have h3 : Real.log x * Real.log x ≤ x * Real.log x * x :=
            (mul_le_mul_of_nonneg_right hLx hL0).trans (le_mul_of_one_le_right hxL hx1)
          have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg C1)
          linarith
  have hpos1 : 0 ≤ C3 ^ 2 * (x * Real.log x) := mul_nonneg (sq_nonneg _) hxL
  have hpos2 : 0 ≤ |C2| * |C3| * (x * Real.log x) := mul_nonneg (mul_nonneg hC2 hC3) hxL
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
