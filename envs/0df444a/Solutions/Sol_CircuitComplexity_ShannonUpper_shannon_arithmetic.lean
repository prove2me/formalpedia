-- Prove2me | solution 1 for CircuitComplexity.ShannonUpper.shannon_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:41.010801+00:00
-- url     : https://prove2.me/submissions/44b44ea0-c8ae-4bab-81c8-697c5829cd23

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
section
@[expose] public section
namespace CircuitComplexity
namespace ShannonUpper
private theorem log_ge_one (N : Nat) (hN : 16 ≤ N) : 1 ≤ Nat.log 2 N :=
  Nat.le_log_of_pow_le (by omega) (by omega)
private theorem pow_split (N : Nat) (hN : 16 ≤ N) :
    2 ^ dataBits N * 2 ^ addrBits N = 2 ^ N := by
  rw [← Nat.pow_add]; congr 1; exact addr_data_sum N hN
private theorem two_mul_pow_addr_le (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N ≤ N := by
  unfold addrBits
  have hlog := log_ge_one N hN
  have : 2 * 2 ^ (Nat.log 2 N - 1) = 2 ^ Nat.log 2 N := by
    conv_rhs => rw [show Nat.log 2 N = (Nat.log 2 N - 1) + 1 from by omega]
    rw [Nat.pow_succ]; ring
  rw [this]; exact Nat.pow_log_le_self 2 (by omega)
private theorem n_lt_four_pow_addr (N : Nat) (hN : 16 ≤ N) :
    N < 4 * 2 ^ addrBits N := by
  unfold addrBits
  have hlog := log_ge_one N hN
  have : 4 * 2 ^ (Nat.log 2 N - 1) = 2 ^ (Nat.log 2 N + 1) := by
    conv_rhs => rw [show Nat.log 2 N + 1 = (Nat.log 2 N - 1) + 2 from by omega]
    rw [Nat.pow_add]; omega
  rw [this]; exact Nat.lt_pow_succ_log_self (by omega) N
private theorem two_n_plus_one_le (N : Nat) (hN : 4 ≤ N) : 2 * N + 1 ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 4 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := @Nat.lt_pow_self n 2 (by omega)
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega
private theorem sq_le_pow (N : Nat) (hN : 16 ≤ N) : N * N ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 16 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := two_n_plus_one_le n (by omega)
      have hsq : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega
private theorem term1 (N : Nat) (hN : 16 ≤ N) :
    4 * 2 ^ dataBits N * N ≤ 16 * 2 ^ N := by
  have hlt := n_lt_four_pow_addr N hN
  have hsplit := pow_split N hN
  have : 4 * 2 ^ dataBits N * N ≤ 4 * 2 ^ dataBits N * (4 * 2 ^ addrBits N) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith [this, hsplit]
private theorem term2 (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N * N ≤ 2 ^ N := by
  calc 2 * 2 ^ addrBits N * N
      ≤ N * N := by apply Nat.mul_le_mul_right; exact two_mul_pow_addr_le N hN
    _ ≤ 2 ^ N := sq_le_pow N hN
private theorem pow_ge_four_mul (k : Nat) (hk : 4 ≤ k) : 4 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 4 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := @Nat.lt_pow_self n 2 (by omega)
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega
private theorem log_le_quarter (N : Nat) (hN : 16 ≤ N) : 4 * Nat.log 2 N ≤ N := by
  have hlog4 : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  calc 4 * Nat.log 2 N
      ≤ 2 ^ Nat.log 2 N := pow_ge_four_mul (Nat.log 2 N) hlog4
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)
private theorem pow_addr_plus_addr_le (N : Nat) (hN : 16 ≤ N) :
    2 ^ addrBits N + addrBits N + (Nat.log 2 N + 1) ≤ N := by
  unfold addrBits
  have hlog1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  have : 2 * 2 ^ (Nat.log 2 N - 1) = 2 ^ Nat.log 2 N := by
    conv_rhs => rw [show Nat.log 2 N = (Nat.log 2 N - 1) + 1 from by omega]
    rw [Nat.pow_succ]; ring
  have : 2 * 2 ^ (Nat.log 2 N - 1) ≤ N := by
    rw [this]; exact Nat.pow_log_le_self 2 (by omega)
  have := log_le_quarter N hN
  omega
private theorem term3 (N : Nat) (hN : 16 ≤ N) :
    2 ^ (2 ^ addrBits N + addrBits N) * N ≤ 2 ^ N := by
  have hkey := pow_addr_plus_addr_le N hN
  have hsub : Nat.log 2 N + 1 ≤ N - (2 ^ addrBits N + addrBits N) := by omega
  have hN_lt : N < 2 ^ (N - (2 ^ addrBits N + addrBits N)) :=
    calc N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
      _ ≤ 2 ^ (N - (2 ^ addrBits N + addrBits N)) := Nat.pow_le_pow_right (by omega) hsub
  have hsplit : 2 ^ (2 ^ addrBits N + addrBits N) *
      2 ^ (N - (2 ^ addrBits N + addrBits N)) = 2 ^ N := by
    rw [← Nat.pow_add]; congr 1; omega
  have : 2 ^ (2 ^ addrBits N + addrBits N) * N ≤
      2 ^ (2 ^ addrBits N + addrBits N) * 2 ^ (N - (2 ^ addrBits N + addrBits N)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega
end ShannonUpper
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.ShannonUpper
namespace CircuitComplexity.ShannonUpper
theorem _root_.solution (N : Nat) (hN : 16 ≤ N) :
    (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
      2 ^ (2 ^ addrBits N + addrBits N)) * N ≤ 18 * 2 ^ N := by
  have h1 := term1 N hN
  have h2 := term2 N hN
  have h3 := term3 N hN
  nlinarith
end CircuitComplexity.ShannonUpper
