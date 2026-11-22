-- Prove2me | solution 1 for CircuitComplexity.arith_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:40.343812+00:00
-- url     : https://prove2.me/submissions/76328f53-485c-4753-9265-ccf36b5ac1ad

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Theorems.Thm_CircuitComplexity_n_plus_s_lt
public import Theorems.Thm_CircuitComplexity_mul_s_lt_two_pow

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N : Nat) (hN : 6 ≤ N) :
    (8 * (N + 2 ^ N / (5 * N)) ^ 2) ^ (2 ^ N / (5 * N)) < 2 ^ 2 ^ N := by
  set s := 2 ^ N / (5 * N)
  have hspos : 0 < s := s_pos N hN
  have h1 : 8 * (N + s) ^ 2 < 2 ^ (2 * N + 3) := by
    have hns : N + s < 2 ^ N := n_plus_s_lt N hN
    have hsq : (N + s) ^ 2 < (2 ^ N) ^ 2 := Nat.pow_lt_pow_left hns (by omega)
    have : 2 ^ (2 * N + 3) = 8 * (2 ^ N) ^ 2 := by rw [← Nat.pow_mul, Nat.pow_add]; ring_nf
    omega
  have h2 : (2 * N + 3) * s < 2 ^ N := mul_s_lt_two_pow N hN
  calc (8 * (N + s) ^ 2) ^ s
      < (2 ^ (2 * N + 3)) ^ s := Nat.pow_lt_pow_left h1 (by omega)
    _ = 2 ^ ((2 * N + 3) * s) := by rw [← Nat.pow_mul]
    _ < 2 ^ (2 ^ N) := Nat.pow_lt_pow_right (by omega) h2
end CircuitComplexity
