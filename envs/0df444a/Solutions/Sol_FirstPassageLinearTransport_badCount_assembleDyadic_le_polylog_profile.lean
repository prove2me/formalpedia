-- Prove2me | solution 1 for FirstPassageLinearTransport.badCount_assembleDyadic_le_polylog_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:26.974804+00:00
-- url     : https://prove2.me/submissions/7ee3de0a-557c-4d0e-834c-8d576a0d5789

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_badCount_le_shell_sum
import Theorems.Thm_FirstPassageLinearTransport_card_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBad_assembleDyadic
import Theorems.Thm_FirstPassageLinearTransport_shellBad_card_eq_ratio_mul
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_sum_two_pow_range
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (B kappa : ℝ)
    (hB : 0 ≤ B) (hkappa : 0 ≤ kappa)
    (hshell : ∀ M, M₀ ≤ M →
      shellExceptionalRatio (S M) M ≤
        B * (((M : ℝ) + 2) ^ (-kappa)))
    (hN : 0 < N) (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
        2 * B * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
  classical
  let L := Nat.log 2 N
  let K := L / 2
  have hKL : K ≤ L + 1 := by
    dsimp [K]
    omega
  have hprefix := badCount_le_shell_sum (assembleDyadic S) N
  have hprefixR :
      (badCount (assembleDyadic S) N : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) := by
    dsimp [L]
    exact_mod_cast hprefix
  rw [← Finset.sum_range_add_sum_Ico
    (fun M => ((shellBad (assembleDyadic S) M).card : ℝ)) hKL] at hprefixR
  have hearly :
      ∑ M ∈ Finset.range K,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (2 : ℝ) ^ K := by
    calc
      ∑ M ∈ Finset.range K,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        ∑ M ∈ Finset.range K, (2 : ℝ) ^ M := by
          apply Finset.sum_le_sum
          intro M hM
          have hcard : (shellBad (assembleDyadic S) M).card ≤ 2 ^ M := by
            calc
              (shellBad (assembleDyadic S) M).card ≤
                  (dyadicShell M).card := by
                apply Finset.card_le_card
                intro n hn
                exact (Finset.mem_filter.mp hn).1
              _ = 2 ^ M := card_dyadicShell M
          exact_mod_cast hcard
      _ = (2 : ℝ) ^ K - 1 := sum_two_pow_range K
      _ ≤ (2 : ℝ) ^ K := by linarith
  have hlatePoint : ∀ M ∈ Finset.Ico K (L + 1),
      ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 : ℝ) ^ M := by
    intro M hM
    have hKM : K ≤ M := (Finset.mem_Ico.mp hM).1
    have hM₀M : M₀ ≤ M := hM₀.trans hKM
    have hratio := hshell M hM₀M
    have hbase : (K : ℝ) + 2 ≤ (M : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right hKM 2
    have hpow :
        ((M : ℝ) + 2) ^ (-kappa) ≤
          ((K : ℝ) + 2) ^ (-kappa) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    have hratio' :
        shellExceptionalRatio (S M) M ≤
          B * (((K : ℝ) + 2) ^ (-kappa)) :=
      hratio.trans (mul_le_mul_of_nonneg_left hpow hB)
    rw [shellBad_assembleDyadic, shellBad_card_eq_ratio_mul]
    exact mul_le_mul_of_nonneg_right hratio' (by positivity)
  have hlate :
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 : ℝ) ^ (L + 1) := by
    calc
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        ∑ M ∈ Finset.Ico K (L + 1),
          (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 : ℝ) ^ M := by
            exact Finset.sum_le_sum hlatePoint
      _ = (B * (((K : ℝ) + 2) ^ (-kappa))) *
          ∑ M ∈ Finset.Ico K (L + 1), (2 : ℝ) ^ M := by
            rw [Finset.mul_sum]
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) *
          ∑ M ∈ Finset.range (L + 1), (2 : ℝ) ^ M := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro M hM
              exact Finset.mem_range.2 (Finset.mem_Ico.mp hM).2
            · intro M hM _
              positivity
      _ = (B * (((K : ℝ) + 2) ^ (-kappa))) *
          ((2 : ℝ) ^ (L + 1) - 1) := by
            rw [sum_two_pow_range]
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) *
          (2 : ℝ) ^ (L + 1) := by
            gcongr
            linarith
  have hpowL : (2 : ℝ) ^ L ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hpowSucc : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    rw [pow_succ]
    nlinarith
  have hlate' :
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        2 * B * N * (((K : ℝ) + 2) ^ (-kappa)) := by
    calc
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) *
          (2 : ℝ) ^ (L + 1) := hlate
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 * N) :=
        mul_le_mul_of_nonneg_left hpowSucc
          (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
      _ = 2 * B * N * (((K : ℝ) + 2) ^ (-kappa)) := by ring
  calc
    (badCount (assembleDyadic S) N : ℝ) ≤
        ∑ M ∈ Finset.range K,
            ((shellBad (assembleDyadic S) M).card : ℝ) +
          ∑ M ∈ Finset.Ico K (L + 1),
            ((shellBad (assembleDyadic S) M).card : ℝ) := hprefixR
    _ ≤ (2 : ℝ) ^ K +
        2 * B * N * (((K : ℝ) + 2) ^ (-kappa)) :=
      add_le_add hearly hlate'
    _ = (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
        2 * B * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
      rfl
end FirstPassageLinearTransport
