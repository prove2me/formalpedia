-- Prove2me | solution 1 for Erdos684.badPrimeWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:02:40.604825+00:00
-- url     : https://prove2.me/submissions/4403dc30-0e69-4cca-a2d1-eecbee0e1c91

module
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_BadPrimes
public import Theorems.Thm_Erdos684_badPrime_dvd_intervalProduct

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution (n X A : ℕ) (hn : 0 < n) :
    ∑ p ∈ badPrimes n X A, Real.log (p : ℝ) ≤
      (A : ℝ) * Real.log (n + A : ℕ) := by
  let B := badPrimes n X A
  let P : ℕ := ∏ p ∈ B, p
  let Q : ℕ := ∏ j ∈ Finset.Icc 1 A, (n + j)
  have hQpos : 0 < Q := by
    exact Finset.prod_pos fun j _ => Nat.add_pos_left hn j
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).pos
  have hsubset : B ⊆ Q.primeFactors := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    exact hprime.mem_primeFactors (badPrime_dvd_intervalProduct hp) hQpos.ne'
  have hdiv : P ∣ Q :=
    (Finset.prod_dvd_prod_of_subset B Q.primeFactors (fun p => p) hsubset).trans
      (Nat.prod_primeFactors_dvd Q)
  have hPQ : P ≤ Q := Nat.le_of_dvd hQpos hdiv
  have hlogP : Real.log (P : ℝ) = ∑ p ∈ B, Real.log (p : ℝ) := by
    dsimp [P]
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).ne_zero
  have hlogQ : Real.log (Q : ℝ) =
      ∑ j ∈ Finset.Icc 1 A, Real.log (n + j : ℕ) := by
    dsimp [Q]
    rw [Nat.cast_prod, Real.log_prod]
    intro j _
    exact_mod_cast (Nat.add_pos_left hn j).ne'
  calc
    ∑ p ∈ badPrimes n X A, Real.log (p : ℝ) = Real.log (P : ℝ) := hlogP.symm
    _ ≤ Real.log (Q : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hPpos) (Nat.cast_le.mpr hPQ)
    _ = ∑ j ∈ Finset.Icc 1 A, Real.log (n + j : ℕ) := hlogQ
    _ ≤ ∑ _j ∈ Finset.Icc 1 A, Real.log (n + A : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.log_le_log (Nat.cast_pos.mpr (Nat.add_pos_left hn j))
      exact Nat.cast_le.mpr (Nat.add_le_add_left (Finset.mem_Icc.mp hj).2 n)
    _ = (A : ℝ) * Real.log (n + A : ℕ) := by simp
end Erdos684
