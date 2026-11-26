-- Prove2me | solution 1 for FirstPassageLinearTransport.QuantitativeDensity.badCount_assembleDyadic_le_stretched_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:26.031475+00:00
-- url     : https://prove2.me/submissions/34690693-1b16-4ec4-8857-6d8447da1cfd

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_stretchedDyadicRate_pos
import Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_badCount_assembleDyadic_le_stretched_rate
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
set_option maxHeartbeats 1000000
open FirstPassageLinearTransport
open FirstPassageLinearTransport.QuantitativeDensity
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport.QuantitativeDensity
theorem _root_.solution
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (A c alpha : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hshell :
      ∀ M, M₀ ≤ M →
        shellExceptionalRatio (S M) M ≤
          A * Real.exp
            (-c * (stretchedShellScale M) ^ alpha))
    (hN : 0 < N)
    (hL2 : 2 ≤ Nat.log 2 N)
    (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (1 + 2 * A) * N *
        Real.exp
          (-(stretchedDyadicRate c / 2) *
            (Real.log N) ^ alpha) := by
  let L := Nat.log 2 N
  have hbase :=
    badCount_assembleDyadic_le_stretched_rate
      S M₀ N A c alpha hA hc halpha0 halpha1 hshell
      hN (by omega) hM₀
  have hNupperNat : N < 2 ^ (L + 1) := by
    dsimp [L]
    exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hNupper : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast hNupperNat.le
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogUpper :
      Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hNR0)
        (Set.mem_Ioi.mpr
          (by positivity : 0 < (2 : ℝ) ^ (L + 1)))
        hNupper
    rw [Real.log_pow] at h
    push_cast at h
    simpa [mul_comm] using h
  have hL2R : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have hlogTwoLt : Real.log 2 < 1 :=
    (Real.log_two_lt_d9).trans (by norm_num)
  have hlogTwoL :
      Real.log N ≤ 2 * (L : ℝ) := by
    nlinarith
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hlogN0 : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have htwo :
      (2 : ℝ) ^ alpha ≤ 2 := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) halpha1
    simpa using h
  have hpowCompare :
      (Real.log N) ^ alpha ≤
        2 * (L : ℝ) ^ alpha := by
    calc
      (Real.log N) ^ alpha
          ≤ (2 * (L : ℝ)) ^ alpha :=
        Real.rpow_le_rpow hlogN0 hlogTwoL halpha0.le
      _ = (2 : ℝ) ^ alpha * (L : ℝ) ^ alpha := by
        rw [Real.mul_rpow (by norm_num) hL0]
      _ ≤ 2 * (L : ℝ) ^ alpha :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hL0 _)
  have hexpCompare :
      Real.exp
          (-(stretchedDyadicRate c) *
            (L : ℝ) ^ alpha) ≤
        Real.exp
          (-(stretchedDyadicRate c / 2) *
            (Real.log N) ^ alpha) := by
    apply Real.exp_le_exp.2
    have hrate0 := stretchedDyadicRate_pos hc
    nlinarith
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hexpCompare
      (mul_nonneg
        (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hA))
        (Nat.cast_nonneg N)))
end FirstPassageLinearTransport.QuantitativeDensity
