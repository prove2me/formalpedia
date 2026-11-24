-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.final_contra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:39.631456+00:00
-- url     : https://prove2.me/submissions/932e7ffb-a90c-4e3f-b153-81413ce1131c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_pow_small_a
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_pow_small_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (q A K0 a b l : ℝ) (K : ℕ) (hq0 : 0 < q) (hq : q ≤ 1 / 4) (hl : l = -Real.log q)
    (hA : 1 ≤ A) (hK3 : 3 ≤ K) (hK0 : 0 < K0) (ha0 : 0 ≤ a) (ha : a * (2 * l + 2) ≤ 1) (hb : 0 ≤ b)
    (hKab : (K : ℝ) ≤ a * K0 + b) (hbig : b + 64 * A * Real.exp (l * b) < K0)
    (hmain : q ^ K ≤ 2 * A * K * Real.exp (-K0) + K * (q ^ 2 / 8) ^ (K - 1) + K * (q / 4) ^ K) : False := by
  have h1 := pow_small_a q hq0.le (by linarith) K hK3
  have h2 := pow_small_b q hq0.le K hK3
  have hl0 : 0 ≤ l := by
    rw [hl]; have := Real.log_nonpos hq0.le (by linarith); linarith
  have h3 : (3 / 4) * q ^ K ≤ 2 * A * K * Real.exp (-K0) := by linarith
  have hqK : Real.exp (-(K0 / 2) - l * b) ≤ q ^ K := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq0, Real.exp_le_exp]
    have hlog : Real.log q = -l := by rw [hl]; ring
    rw [hlog]
    have hla : 2 * l * a ≤ 1 := by nlinarith
    nlinarith
  have hE := Real.exp_pos (l * b)
  have hsplit : Real.exp (-(K0 / 2) - l * b) * Real.exp (l * b) * Real.exp K0 = Real.exp (K0 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hexp : K0 ^ 2 / 8 ≤ Real.exp (K0 / 2) := by
    have := Real.pow_div_factorial_le_exp (x := K0 / 2) (by positivity) 2
    norm_num [Nat.factorial] at this; nlinarith
  have hKK : (K : ℝ) ≤ 2 * K0 := by
    have : a ≤ 1 / 2 := by nlinarith
    nlinarith
  have hexpK : Real.exp (-K0) * Real.exp K0 = 1 := by rw [← Real.exp_add]; simp

  have h4 : (3 / 4) * Real.exp (K0 / 2) ≤ 2 * A * K * Real.exp (l * b) := by
    have hx := mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_left hqK (by norm_num)) h3)
      (le_of_lt (mul_pos hE (Real.exp_pos K0)))
    rw [← hsplit]
    have : 2 * A * K * Real.exp (-K0) * (Real.exp (l * b) * Real.exp K0) = 2 * A * K * Real.exp (l * b) * (Real.exp (-K0) * Real.exp K0) := by ring
    rw [this, hexpK] at hx
    linarith
  have hAE : 0 ≤ A * Real.exp (l * b) := by positivity
  have h5 : (3 / 32) * K0 ^ 2 ≤ 4 * K0 * (A * Real.exp (l * b)) := by nlinarith
  have h6 : (3 / 32) * K0 ≤ 4 * (A * Real.exp (l * b)) := by nlinarith
  nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
