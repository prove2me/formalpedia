-- Prove2me | solution 1 for FirstPassageLinearTransport.two_affineConstant_le_n_mul_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:33.382412+00:00
-- url     : https://prove2.me/submissions/23a32eba-dd02-476e-83cb-65e0f175c365

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_eq_two_rpow_logTwoThree
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_ge_n_rpow_neg_gap
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k M : ℕ} (hM : 4 ≤ M) (hkM : k ≤ M)
    (hnShell : n ∈ dyadicShell M) :
    2 * (2 + Real.sqrt 3) ≤ (n : ℝ) * centralOrbitScale k := by
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hconst : 2 * (2 + Real.sqrt 3) ≤ (9 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3]
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hnPos : 0 < n := by
    exact lt_of_lt_of_le (pow_pos (by omega) M) hnLowerNat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hscale := centralOrbitScale_ge_n_rpow_neg_gap hkM hnShell
  have h16 : (16 : ℝ) ≤ n := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hM
      _ ≤ n := hnLower
  have hnA0 : (16 : ℝ) ^ a0 ≤ (n : ℝ) ^ a0 :=
    Real.rpow_le_rpow (by norm_num) h16 a0_pos.le
  have h16a0 : (16 : ℝ) ^ a0 = 9 := by
    calc
      (16 : ℝ) ^ a0 = (2 : ℝ) ^ (4 * a0) := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      _ = (3 : ℝ) ^ (2 : ℝ) := by
        rw [three_rpow_eq_two_rpow_logTwoThree]
        congr 1
        unfold a0
        ring
      _ = 9 := by norm_num
  have hA0Scale : (n : ℝ) ^ a0 ≤ (n : ℝ) * centralOrbitScale k := by
    have hExp : a0 = 1 + (-driftGap) := by
      unfold driftGap
      ring
    rw [hExp, Real.rpow_add hnR, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hscale hnR.le
  calc
    2 * (2 + Real.sqrt 3) ≤ 9 := hconst
    _ = (16 : ℝ) ^ a0 := h16a0.symm
    _ ≤ (n : ℝ) ^ a0 := hnA0
    _ ≤ (n : ℝ) * centralOrbitScale k := hA0Scale
end FirstPassageLinearTransport
