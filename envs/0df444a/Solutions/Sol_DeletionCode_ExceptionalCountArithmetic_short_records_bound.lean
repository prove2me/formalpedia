-- Prove2me | solution 1 for DeletionCode.ExceptionalCountArithmetic.short_records_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:56.213726+00:00
-- url     : https://prove2.me/submissions/0da32e17-fc5f-4c40-b0ce-36598bfa57f6

import Definitions.Def_DeletionCode_FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic

set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalCountArithmetic
theorem _root_.solution (n t : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) := by
  calc
    _ ≤ ∑ _d ∈ Finset.range t, 4 ^ (2 * t) * n ^ (2 * t - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdt : d < t := Finset.mem_range.mp hd
      have he : 2 * d ≤ 2 * t - 1 := by omega
      have hn' : n ^ (2 * d) ≤ n ^ (2 * t - 1) := pow_le_pow_right₀ hn he
      have hfour : (4 : ℕ) ^ (2 * d) ≤ 4 ^ (2 * t) :=
        pow_le_pow_right₀ (by decide) (by omega)
      calc
        _ ≤ n ^ (2 * t - 1) * 4 ^ (2 * t) := Nat.mul_le_mul hn' hfour
        _ = _ := Nat.mul_comm _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
end DeletionCode.ExceptionalCountArithmetic
