-- Prove2me | solution 1 for Finset.exists_le_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:00.903646+00:00
-- url     : https://prove2.me/submissions/6c2b16ad-5436-4957-96ab-1e73766ba7ad

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_bernoulliWeight_nonneg
public import Theorems.Thm_Finset_sum_bernoulliWeight
section
@[expose] public section
open Finset
namespace Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
private theorem exists_bernoulliWeight_pos (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ A ∈ U.powerset, 0 < U.bernoulliWeight p A := by
  rcases h1.lt_or_eq with h1 | rfl
  · exact ⟨∅, empty_mem_powerset U, by
      rw [bernoulliWeight, card_empty, pow_zero, one_mul, sdiff_empty]
      exact pow_pos (by linarith) _⟩
  · exact ⟨U, mem_powerset_self U, by simp [bernoulliWeight]⟩
end Finset
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Finset α → ℝ) :
    ∃ A ∈ U.powerset, f A ≤ ∑ B ∈ U.powerset, U.bernoulliWeight p B * f B := by
  by_contra! h
  obtain ⟨A₀, hA₀, hpos⟩ := exists_bernoulliWeight_pos (U := U) h0 h1
  have hlt : ∑ B ∈ U.powerset, U.bernoulliWeight p B * (∑ C ∈ U.powerset,
      U.bernoulliWeight p C * f C) < ∑ B ∈ U.powerset, U.bernoulliWeight p B * f B :=
    sum_lt_sum (fun B hB => mul_le_mul_of_nonneg_left (h B hB).le
      (bernoulliWeight_nonneg h0 h1 B)) ⟨A₀, hA₀, mul_lt_mul_of_pos_left (h A₀ hA₀) hpos⟩
  rw [← sum_mul, sum_bernoulliWeight, one_mul] at hlt
  exact lt_irrefl _ hlt
end Finset
