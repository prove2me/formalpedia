-- Prove2me | solution 1 for Finset.exists_forall_not_of_sum_bernoulliProb_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:02.319035+00:00
-- url     : https://prove2.me/submissions/7c2d4384-68d8-4795-8198-e4c422acef40

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_exists_le_expectation
public import Theorems.Thm_Finset_expectation_card_filter

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution {ι : Type*} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (I : Finset ι) (E : ι → Finset α → Prop) [∀ i, DecidablePred (E i)]
    (h : ∑ i ∈ I, U.bernoulliProb p (E i) < 1) :
    ∃ A ∈ U.powerset, ∀ i ∈ I, ¬E i A := by
  obtain ⟨A, hA, hle⟩ := exists_le_expectation h0 h1 fun A => (#{i ∈ I | E i A} : ℝ)
  refine ⟨A, hA, fun i hi hiA => ?_⟩
  rw [expectation_card_filter] at hle
  have hone : (1 : ℝ) ≤ #{i ∈ I | E i A} := by
    exact_mod_cast card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hiA⟩⟩
  linarith
end Finset
