-- Prove2me | solution 1 for Erdos266.one_le_bigM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:42:59.08205+00:00
-- url     : https://prove2.me/submissions/aefe2406-ca89-4b67-9871-53df5df35a7c

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_one_le_bigN
public import Theorems.Thm_Erdos266_succ_le_two_pow

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) : 1 ≤ bigM k := by
  rw [bigM, le_min_iff]
  constructor
  · -- N k ≥ 4k, so the quotient is at least 1
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : k + 2 ≤ k ^ 2 := by nlinarith
    calc 1 * (4 * k) = 4 * k := by ring
    _ ≤ 4 * 2 ^ k := by
        have := succ_le_two_pow k
        omega
    _ = 2 ^ (k + 2) := by ring
    _ ≤ 2 ^ (k ^ 2) := Nat.pow_le_pow_right (by norm_num) h1
    _ = bigN k := rfl
  · -- √(N k) ≥ 1 since N k ≥ 1
    have h := one_le_bigN k
    exact Nat.le_sqrt.mpr (by omega)
end Erdos266
