-- Prove2me | solution 1 for Erdos685.primeFactors_card_le_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:42:01.345838+00:00
-- url     : https://prove2.me/submissions/979ee474-baf7-4cae-9ce8-cc62e69630f3

module
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Asymptotic_PrimeCutoff

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open Erdos685
namespace Erdos685
theorem _root_.solution {B : ℕ} (hB : 0 < B)
    {T : ℝ} (hT : 1 < T) :
    (B.primeFactors.card : ℝ) ≤ T + 1 + Real.log B / Real.log T := by
  classical
  let s : Finset ℕ := B.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ T)
  let l : Finset ℕ := B.primeFactors.filter (fun p : ℕ ↦ ¬ (p : ℝ) ≤ T)
  have hsmall : (s.card : ℝ) ≤ T + 1 := by
    have hsub : s ⊆ Finset.range (⌊T⌋₊ + 1) := by
      intro p hp
      have hpT : (p : ℝ) ≤ T := (Finset.mem_filter.mp hp).2
      apply Finset.mem_range.mpr
      have hpcast : (p : ℝ) < (⌊T⌋₊ : ℝ) + 1 :=
        hpT.trans_lt (Nat.lt_floor_add_one T)
      exact_mod_cast hpcast
    have hcard : s.card ≤ ⌊T⌋₊ + 1 := by
      simpa using Finset.card_le_card hsub
    have hcard' : (s.card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
    linarith [Nat.floor_le (show 0 ≤ T by linarith)]
  have hprime (p : ℕ) (hp : p ∈ B.primeFactors) : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hprodpos : 0 < (∏ p ∈ B.primeFactors, (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact lt_of_lt_of_le zero_lt_one (hprime p hp)
  have hprodle : (∏ p ∈ B.primeFactors, (p : ℝ)) ≤ (B : ℝ) := by
    have hnat : (∏ p ∈ B.primeFactors, p) ≤ B :=
      Nat.le_of_dvd hB (Nat.prod_primeFactors_dvd B)
    have hcast : ((∏ p ∈ B.primeFactors, p : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_prod] using hcast
  have hsum : (∑ p ∈ B.primeFactors, Real.log (p : ℝ)) ≤ Real.log B := by
    rw [← Real.log_prod (fun p hp ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (hprime p hp)))]
    exact Real.log_le_log hprodpos hprodle
  have hlarge : (l.card : ℝ) * Real.log T ≤ Real.log B := by
    calc
      (l.card : ℝ) * Real.log T = ∑ _p ∈ l, Real.log T := by simp
      _ ≤ ∑ p ∈ l, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpT : T < (p : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hp).2
        exact Real.log_le_log (by linarith) hpT.le
      _ ≤ ∑ p ∈ B.primeFactors, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (show l ⊆ B.primeFactors from Finset.filter_subset _ _)
        intro p hp _
        exact Real.log_nonneg (hprime p hp)
      _ ≤ Real.log B := hsum
  have hlarge' : (l.card : ℝ) ≤ Real.log B / Real.log T :=
    (le_div_iff₀ (Real.log_pos hT)).mpr hlarge
  have hcard : s.card + l.card = B.primeFactors.card := by
    exact Finset.card_filter_add_card_filter_not (fun p : ℕ ↦ (p : ℝ) ≤ T)
  have hcard' : (s.card : ℝ) + (l.card : ℝ) = (B.primeFactors.card : ℝ) := by
    exact_mod_cast hcard
  linarith
end Erdos685
