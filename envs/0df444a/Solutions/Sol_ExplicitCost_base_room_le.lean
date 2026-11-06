-- Prove2me | solution 1 for ExplicitCost.base_room_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:29.271083+00:00
-- url     : https://prove2.me/submissions/dd453354-ba84-426e-9222-c567c9000f59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Base
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_nat
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {K lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (hB : 1 ≤ B) :
    3 * (2 * lam + 1 + (2 * B + 1)) + 3 * (K * (K - 1) / 2 * lam) + 2 * (B * K) + 2 * size K + K * (2 * lam + 2) + B + 13 + 1 ≤ (K * (lam + B)) ^ 6 := by
  obtain ⟨X, hX⟩ : ∃ X, X = K * (lam + B) := ⟨_, rfl⟩
  rw [← hX]
  have e1 : X = K * lam + K * B := by rw [hX, Nat.mul_add]
  have a1 : lam ≤ K * lam := Nat.le_mul_of_pos_left _ hK
  have a2 : B ≤ K * B := Nat.le_mul_of_pos_left _ hK
  have a3 : K ≤ K * B := Nat.le_mul_of_pos_right _ hB
  have a4 : K * (K - 1) / 2 * lam ≤ X * X := by
    have b1 : K * (K - 1) / 2 ≤ K * K := (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    calc K * (K - 1) / 2 * lam ≤ K * K * lam := Nat.mul_le_mul_right _ b1
      _ = K * (K * lam) := Nat.mul_assoc _ _ _
      _ ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have a5 : size K ≤ K + 1 := by
    have := Nat.size_le.2 (Nat.lt_two_pow_self (n := K))
    rw [size_nat]
    omega
  have a6 : K * (2 * lam + 2) = 2 * (K * lam) + 2 * K := by ring
  have a7 : B * K = K * B := Nat.mul_comm _ _
  have h2 : 2 ≤ X := by omega
  have a8 : 2 * X ≤ X * X := Nat.mul_le_mul_right _ h2
  have a9 : 16 * (X * X) ≤ X ^ 6 := by
    have : 2 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left h2 4
    calc 16 * (X * X) = 2 ^ 4 * (X * X) := by norm_num
      _ ≤ X ^ 4 * (X * X) := Nat.mul_le_mul_right _ this
      _ = X ^ 6 := by ring
  rw [a6, a7]
  omega
end ExplicitCost
