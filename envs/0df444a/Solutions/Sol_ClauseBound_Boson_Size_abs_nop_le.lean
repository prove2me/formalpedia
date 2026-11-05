-- Prove2me | solution 1 for ClauseBound.Boson.Size.abs_nop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:40.840867+00:00
-- url     : https://prove2.me/submissions/fd7ab11c-1978-4aa7-9aef-f34bec1b0bc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
import Theorems.Thm_ClauseBound_Boson_Size_abs_bet_le
import Theorems.Thm_ClauseBound_Boson_Size_le_sum_of_mem
import Theorems.Thm_ClauseBound_Boson_Size_sum_erase_le
import Theorems.Thm_ClauseBound_Boson_Size_card_toFinset_le
import Theorems.Thm_ClauseBound_Boson_Size_sum_mul_count

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size
namespace ClauseBound.Boson.Size
theorem _root_.solution {W n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) {F : ℤ → Ker} {B : ℤ} (hB : 0 ≤ B)
    (hF : ∀ (r : ℤ) (π σ : Multiset ℕ), π.sum ≤ W → σ.sum ≤ W → |F r π σ| ≤ B) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |nop n F r π σ| ≤ 2 ^ (4 * W + 1) * B := by
  have hp : (0 : ℤ) ≤ 2 ^ (2 * W) := by positivity
  have h1 : |∑ l ∈ π.toFinset, bet n l * cre l (F (r - l)) π σ| ≤ ((W : ℤ) + 1) * (2 ^ (2 * W) * B) := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_card_nsmul _ _ (2 ^ (2 * W) * B) fun l hl => ?_).trans ?_)
    · have hl' := Multiset.mem_toFinset.1 hl
      have hlW : l ≤ W := (le_sum_of_mem hl').trans hπ
      rw [abs_mul, cre, if_pos hl']
      exact mul_le_mul (abs_bet_le hW hn (by omega) (by exact_mod_cast hlW)) (hF _ _ _ ((sum_erase_le π l).trans hπ) hσ) (abs_nonneg _) hp
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_toFinset_le hπ) (mul_nonneg hp hB)
  have h2 : |∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ| ≤ (W : ℤ) * (2 ^ (2 * W) * B) := by
    calc |∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ|
        ≤ ∑ k ∈ σ.toFinset, ((k : ℤ) * (σ.count k : ℤ)) * (2 ^ (2 * W) * B) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
          have hkW : k ≤ W := (le_sum_of_mem (Multiset.mem_toFinset.1 hk)).trans hσ
          have hc : (0 : ℤ) ≤ (k : ℤ) * (σ.count k : ℤ) := by positivity
          rw [abs_mul, ann, abs_mul, abs_of_nonneg hc, mul_left_comm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (abs_bet_le hW hn (by omega) (by omega)) (hF _ _ _ hπ ((sum_erase_le σ k).trans hσ)) (abs_nonneg _) hp) hc
      _ = (σ.sum : ℤ) * (2 ^ (2 * W) * B) := by rw [← sum_mul, sum_mul_count]
      _ ≤ (W : ℤ) * (2 ^ (2 * W) * B) := mul_le_mul_of_nonneg_right (by exact_mod_cast hσ) (mul_nonneg hp hB)
  have h3 : (2 * (W : ℤ) + 1) ≤ 2 ^ (2 * W + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := 2 * W + 1)).le
  calc |nop n F r π σ| ≤ ((W : ℤ) + 1) * (2 ^ (2 * W) * B) + (W : ℤ) * (2 ^ (2 * W) * B) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (2 * (W : ℤ) + 1) * (2 ^ (2 * W) * B) := by ring
    _ ≤ 2 ^ (2 * W + 1) * (2 ^ (2 * W) * B) := mul_le_mul_of_nonneg_right h3 (mul_nonneg hp hB)
    _ = 2 ^ (4 * W + 1) * B := by rw [← mul_assoc, ← pow_add]; congr 2; ring
end ClauseBound.Boson.Size
