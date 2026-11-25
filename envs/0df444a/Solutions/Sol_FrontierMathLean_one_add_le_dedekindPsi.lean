-- Prove2me | solution 1 for FrontierMathLean.one_add_le_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:55:54.691103+00:00
-- url     : https://prove2.me/submissions/91a8f44a-eba2-42d5-92a6-2a66fae7dab8

import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Theorems.Thm_FrontierMathLean_dedekindPsi_zero
import Theorems.Thm_FrontierMathLean_dedekindPsi_one
attribute [local simp] FrontierMathLean.dedekindPsi_zero
attribute [local simp] FrontierMathLean.dedekindPsi_one
section
open Finset
open scoped ArithmeticFunction.sigma
namespace FrontierMathLean
private theorem prime_power_factor_lt {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    p ^ a < p ^ (a - 1) * (p + 1) := by
  have hpow : 0 < p ^ (a - 1) := pow_pos hp.pos _
  have hexp : a - 1 + 1 = a := by omega
  calc
    p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, hexp]
    _ < p ^ (a - 1) * p + p ^ (a - 1) := Nat.lt_add_of_pos_right hpow
    _ = p ^ (a - 1) * (p + 1) := by rw [mul_add, mul_one]
end FrontierMathLean
end

set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ dedekindPsi n := by
  have hn0 : n ≠ 0 := by omega
  have hnonempty : n.primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr (by omega)
  have hlt :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) <
        ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro p hp
      exact pow_pos (Nat.pos_of_mem_primeFactors hp) _
    · intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hdiv := Nat.dvd_of_mem_primeFactors hp
      exact prime_power_factor_lt hprime (hprime.factorization_pos_of_dvd hn0 hdiv)
    · exact hnonempty
  have hlt_n :
      n < ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) := by
    calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Nat.prod_primeFactors_pow_factorization hn0
      _ < _ := hlt
  simpa only [dedekindPsi, if_neg hn0, Nat.succ_le_iff] using hlt_n
end FrontierMathLean
