-- Prove2me | solution 1 for CircuitComplexity.ShannonUpper.shannon_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:32.536058+00:00
-- url     : https://prove2.me/submissions/c2ef8481-9422-4e66-8d15-e6f961b29548

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_arithmetic

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.ShannonUpper
namespace CircuitComplexity.ShannonUpper
theorem _root_.solution (N : Nat) (hN : 16 ≤ N) (G : Nat)
    (hG : G + 1 ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
            2 ^ (2 ^ addrBits N + addrBits N)) :
    G + 1 ≤ 18 * 2 ^ N / N := by
  have hNpos : 0 < N := by omega
  apply (Nat.le_div_iff_mul_le hNpos).mpr
  calc (G + 1) * N
      ≤ (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N)) * N := by
        apply Nat.mul_le_mul_right; exact hG
    _ ≤ 18 * 2 ^ N := shannon_arithmetic N hN
end CircuitComplexity.ShannonUpper
