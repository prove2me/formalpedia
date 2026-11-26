-- Prove2me | solution 1 for FirstPassageLinearTransport.maximizer_is_in_quarter_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:02.793645+00:00
-- url     : https://prove2.me/submissions/9b0b3505-f53c-4daf-9ec7-96131bd0303f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_lt_succ_of_ratio
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_succ_lt_of_ratio
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hpHalf : 1 / 2 < p) (hpTwoThird : p < 2 / 3)
    {n k₀ : ℕ} (hn : 9 ≤ n) (hk₀n : k₀ ≤ n)
    (hmax : ∀ k : ℕ, k ≤ n →
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀) :
    (n : ℝ) / 4 ≤ (k₀ : ℝ) ∧
      (n : ℝ) / 4 ≤ ((n - k₀ : ℕ) : ℝ) := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : p < 1 := by linarith
  constructor
  · by_contra hnot
    have hkLower : (k₀ : ℝ) < (n : ℝ) / 4 := lt_of_not_ge hnot
    have h4cast : (4 * k₀ : ℕ) < n := by
      exact_mod_cast (show (4 : ℝ) * (k₀ : ℝ) < (n : ℝ) by nlinarith)
    have hk₀n' : k₀ < n := by omega
    have hstep : k₀ + 1 ≤ n - k₀ := by omega
    have hratio : ((k₀ + 1 : ℕ) : ℝ) * (1 - p) <
        ((n - k₀ : ℕ) : ℝ) * p := by
      calc
        ((k₀ + 1 : ℕ) : ℝ) * (1 - p) <
            ((k₀ + 1 : ℕ) : ℝ) * p := by
          apply mul_lt_mul_of_pos_left
          · linarith
          · positivity
        _ ≤ ((n - k₀ : ℕ) : ℝ) * p := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hstep) hp₀.le
    have hinc := tiltedBinomialMass_lt_succ_of_ratio hp₀ hp₁ hk₀n' hratio
    exact (not_le_of_gt hinc) (hmax (k₀ + 1) (by omega))
  · by_contra hnot
    have hrLower : ((n - k₀ : ℕ) : ℝ) < (n : ℝ) / 4 :=
      lt_of_not_ge hnot
    have hk₀pos : 0 < k₀ := by
      by_contra hkzero
      have : k₀ = 0 := Nat.eq_zero_of_not_pos hkzero
      subst k₀
      have hnR : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      norm_num only [Nat.sub_zero] at hrLower
      nlinarith
    let j := k₀ - 1
    have hjSucc : j + 1 = k₀ := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hsub : n - j = (n - k₀) + 1 := by dsimp [j]; omega
    have hkLarge : (3 : ℝ) * (n : ℝ) / 4 < (k₀ : ℝ) := by
      have hcast : ((n - k₀ : ℕ) : ℝ) = (n : ℝ) - (k₀ : ℝ) :=
        Nat.cast_sub hk₀n
      nlinarith
    have hnReal : (8 : ℝ) < (n : ℝ) := by exact_mod_cast (show 8 < n by omega)
    have hratio : ((n - j : ℕ) : ℝ) * p <
        ((j + 1 : ℕ) : ℝ) * (1 - p) := by
      rw [hsub, hjSucc, Nat.cast_add, Nat.cast_one]
      calc
        (((n - k₀ : ℕ) : ℝ) + 1) * p <
            ((n : ℝ) / 4 + 1) * p := by
          exact mul_lt_mul_of_pos_right (by linarith) hp₀
        _ < ((n : ℝ) / 4 + 1) * (2 / 3) := by
          exact mul_lt_mul_of_pos_left hpTwoThird (by positivity)
        _ < (n : ℝ) / 4 := by nlinarith
        _ < (k₀ : ℝ) * (1 / 3) := by nlinarith
        _ < (k₀ : ℝ) * (1 - p) := by
          apply mul_lt_mul_of_pos_left
          · linarith
          · positivity
    have hdec := tiltedBinomialMass_succ_lt_of_ratio hp₀ hp₁ hjn hratio
    rw [hjSucc] at hdec
    exact (not_le_of_gt hdec) (hmax j (by dsimp [j]; omega))
end FirstPassageLinearTransport
