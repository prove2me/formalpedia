-- Prove2me | solution 1 for CircuitComplexity.mul_s_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:00.64101+00:00
-- url     : https://prove2.me/submissions/749de25f-e2a8-4f91-afea-f7a4f5a9371a

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
    (2 * N + 3) * (2 ^ N / (5 * N)) < 2 ^ N := by
  calc (2 * N + 3) * (2 ^ N / (5 * N))
      < (5 * N) * (2 ^ N / (5 * N)) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (s_pos N hN)
    _ ≤ 2 ^ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
end CircuitComplexity
