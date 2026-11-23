-- Prove2me | solution 1 for BroughanRH.squarefreeParity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:38:14.175878+00:00
-- url     : https://prove2.me/submissions/870aab3f-1393-4b5c-9e03-eeb0492ff8ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

open Asymptotics Filter ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

lemma brh_card_primeFactors_eq (n : ℕ) : n.primeFactors.card = ω n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

lemma brh_moebius_eq_indicator (n : ℕ) (hn : n ≠ 0) :
    ((μ n : ℤ) : ℝ) = (if Squarefree n ∧ Even n.primeFactors.card then (1 : ℝ) else 0)
      - (if Squarefree n ∧ Odd n.primeFactors.card then (1 : ℝ) else 0) := by
  by_cases hsq : Squarefree n
  · rw [moebius_apply_of_squarefree hsq, ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hn).2 hsq,
      ← brh_card_primeFactors_eq]
    rcases Nat.even_or_odd n.primeFactors.card with h | h
    · have h' : ¬ Odd n.primeFactors.card := Nat.not_odd_iff_even.2 h
      simp [hsq, h, h', h.neg_one_pow]
    · have h' : ¬ Even n.primeFactors.card := Nat.not_even_iff_odd.2 h
      simp [hsq, h, h', h.neg_one_pow]
  · simp [hsq, moebius_eq_zero_of_not_squarefree hsq]

theorem solution :
    let pos (N : ℕ) := (Finset.Icc 1 N).filter fun n => Squarefree n ∧ Even n.primeFactors.card
    let neg (N : ℕ) := (Finset.Icc 1 N).filter fun n => Squarefree n ∧ Odd n.primeFactors.card
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => |((pos N).card : ℝ) - ((neg N).card : ℝ)|) (fun N : ℕ => (N : ℝ)^(1/2+ε)) := by
  intro pos neg ε hε
  have hM := moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis ε hε
  have key : ∀ N : ℕ, ((pos N).card : ℝ) - ((neg N).card : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ) := by
    intro N
    simp only [pos, neg, Finset.card_filter, Nat.cast_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1; omega
    rw [brh_moebius_eq_indicator n hn0]
    split_ifs <;> simp
  refine IsBigO.trans ?_ hM
  refine IsBigO.of_bound 1 (Eventually.of_forall fun N => ?_)
  have hc : (((∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℝ)) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N, ((μ n : ℤ) : ℂ) := by push_cast; rfl
  rw [key N, one_mul, Real.norm_eq_abs, abs_abs, ← hc, Complex.norm_real, Real.norm_eq_abs]
