-- Prove2me | solution 1 for CircuitComplexity.n_plus_s_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:59.195815+00:00
-- url     : https://prove2.me/submissions/a70981ab-34c2-436d-87d3-bea00ebc7f8b

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution (N : Nat) (hN : 6 ≤ N) :
    N + 2 ^ N / (5 * N) < 2 ^ N := by
  have h5n := five_n_le_two_pow N hN
  have hN5 : N ≤ 2 ^ N / 5 := by
    rwa [Nat.le_div_iff_mul_le (by omega : 0 < 5), Nat.mul_comm]
  have hS5 : 2 ^ N / (5 * N) ≤ 2 ^ N / 5 :=
    Nat.div_le_div_left (by omega : 5 ≤ 5 * N) (by omega : 0 < 5)
  have h4 : 2 * (2 ^ N / 5) < 2 ^ N := by
    have hle := Nat.mul_div_le_mul_div_assoc 2 (2 ^ N) 5
    have hlt : 2 * 2 ^ N / 5 < 2 ^ N := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 5)]
      linarith
    omega
  omega
end CircuitComplexity
