-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.final_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:52.844803+00:00
-- url     : https://prove2.me/submissions/b971d976-7b59-4a8e-8a69-bc9d3f341851

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
private theorem rr_pos' (a : ℕ) : 0 < rr a := by
  unfold rr
  positivity
private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]
private theorem succ_cube_le_eight_pow (j : ℕ) : (j + 1) ^ 3 ≤ 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    calc (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * (n + 1) ^ 3 := by ring
      _ ≤ 8 * 8 ^ n := by gcongr
      _ = 8 ^ (n + 1) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) (E G : ℝ) (hE : 0 < E) (hG : 0 < G) (j : ℕ)
    (hj : E * G < j)
    (h : 1 / (E * (rr a / 8) ^ j) ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j) : False := by
  have hb := rr_pos' a
  have hP : 0 < (rr a / 8) ^ j := by positivity
  have hB : 0 < rr a ^ j := by positivity
  have hPB : (rr a / 8) ^ j * 8 ^ j = rr a ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) = 1 :=
    div_mul_cancel_of_ne_zero_real _ _ (mul_pos hE hP).ne'
  have h2 : G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j = G * ((j : ℝ) + 1) ^ 2 :=
    div_mul_cancel_of_ne_zero_real _ _ hB.ne'
  have h3 := mul_le_mul_of_nonneg_right h (mul_pos hE hB).le
  have h4 : (8 : ℝ) ^ j ≤ G * ((j : ℝ) + 1) ^ 2 * E := by
    calc (8 : ℝ) ^ j = 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) * 8 ^ j := by
          rw [h1, one_mul]
      _ = 1 / (E * (rr a / 8) ^ j) * (E * rr a ^ j) := by
          rw [← hPB]
          ring
      _ ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * (E * rr a ^ j) := h3
      _ = G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j * E := by ring
      _ = G * ((j : ℝ) + 1) ^ 2 * E := by rw [h2]
  have hc : ((j : ℝ) + 1) ^ 3 ≤ 8 ^ j := by exact_mod_cast succ_cube_le_eight_pow j
  have hm := mul_lt_mul_of_pos_right hj (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)
  nlinarith [hm, hc, h4, sq_nonneg ((j : ℝ) + 1)]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
