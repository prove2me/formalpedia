-- Prove2me | solution 1 for FirstPassageLinearTransport.maximalBarrier_phase_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:21.832939+00:00
-- url     : https://prove2.me/submissions/3758a721-b275-4b09-8cc7-3422f1b292a7

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_maximalBarrierHeight
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrier_phase_half
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {n M : ℕ} {t : ℝ}
    (ht : 0 < t) (hstart : 2 ≤ t * M)
    (hnShell : n ∈ dyadicShell M) :
    2 * (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by
  have hhalf := maximalBarrier_phase_half ht.le hnShell
  have htwoExp : (1 : ℝ) ≤ t * (M : ℝ) / 2 := by
    linarith
  have htwo : (2 : ℝ) ≤ (n : ℝ) ^ (t / 2) := by
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ (t * (M : ℝ) / 2) := by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) htwoExp
    exact h2pow.trans (by
      rw [← three_rpow_maximalBarrierHeight]
      exact hhalf)
  have hnPos : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hp (mem_dyadicShell.mp hnShell).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  calc
    2 * (3 : ℝ) ^ maximalBarrierHeight t M ≤
        (n : ℝ) ^ (t / 2) * (n : ℝ) ^ (t / 2) :=
      mul_le_mul htwo hhalf (by positivity) (by positivity)
    _ = (n : ℝ) ^ t := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
end FirstPassageLinearTransport
