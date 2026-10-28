-- Prove2me | solution 1 for CPDNetworks.Unknown.grid_card
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:03:59.42012+00:00
-- url     : https://prove2.me/submissions/d3de259c-6bf9-41d1-8545-27621ac89c13

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices
open CPDNetworks.Unknown

theorem solution (T : ℕ) (hT : 2 ≤ T) :
    ((dyadicGrid T).card : ℝ) ≤ 2 * Real.logb 2 T ∧ dyadicGrid T ⊆ DT T := by
  set K := Nat.log 2 (T / 2) with hK
  have hpow : 2 ^ K ≤ T / 2 := Nat.pow_log_le_self 2 (by omega)
  have hpow2 : 2 ^ (K + 1) ≤ T := by
    rw [pow_succ]; have := Nat.div_mul_le_self T 2; omega
  constructor
  · have hc : (dyadicGrid T).card ≤ 2 * (K + 1) := by
      unfold dyadicGrid
      refine (Finset.card_union_le _ _).trans ?_
      have h1 := Finset.card_image_le (s := Finset.range (K + 1)) (f := fun k => 2 ^ k)
      have h2 := Finset.card_image_le (s := Finset.range (K + 1)) (f := fun k => T - 2 ^ k)
      rw [Finset.card_range] at h1 h2
      rw [← hK]; omega
    have hlog : ((K + 1 : ℕ) : ℝ) ≤ Real.logb 2 T := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      rw [Real.rpow_natCast]
      exact_mod_cast hpow2
    have : ((dyadicGrid T).card : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    linarith
  · intro x hx
    unfold dyadicGrid at hx
    unfold DT
    rw [Finset.mem_Icc]
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
    rcases hx with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [Finset.mem_range] at hk
      have : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by rw [← hK] at hk; omega)
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    · rw [Finset.mem_range] at hk
      have : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by rw [← hK] at hk; omega)
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
