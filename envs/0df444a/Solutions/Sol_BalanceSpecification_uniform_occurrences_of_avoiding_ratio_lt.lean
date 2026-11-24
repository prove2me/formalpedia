-- Prove2me | solution 1 for BalanceSpecification.uniform_occurrences_of_avoiding_ratio_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:34.980553+00:00
-- url     : https://prove2.me/submissions/842e6b19-b46f-4322-8d37-39c03d9340f2

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_exists_infix_of_avoiding_ratio_lt

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution {v : Word A} {N : ℕ} {c : ℝ}
    (hR : ∀ u ∈ L, c ≤ ((followerFinset L u N).card : ℝ) / wordCount L N)
    (hP : ∀ u ∈ L, c ≤ ((predecessorFinset L u N).card : ℝ) / wordCount L N)
    (hsmall : (wordCount (avoidingLanguage L v) N : ℝ) / wordCount L N < c) :
    ∀ u ∈ L,
      (∃ s ∈ followerFinset L u N, v <:+: s) ∧
      (∃ p ∈ predecessorFinset L u N, v <:+: p) := by
  classical
  intro u hu
  constructor
  · apply exists_infix_of_avoiding_ratio_lt (Finset.filter_subset _ _)
    exact hsmall.trans_le (hR u hu)
  · apply exists_infix_of_avoiding_ratio_lt (Finset.filter_subset _ _)
    exact hsmall.trans_le (hP u hu)
end BalanceSpecification
