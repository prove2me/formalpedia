-- Prove2me | solution 1 for BalanceSpecification.exists_uniform_occurrences_of_avoidance_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:27.970807+00:00
-- url     : https://prove2.me/submissions/5af1df5c-9471-4589-93f3-42c5a0e4caf8

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_uniform_occurrences_of_avoiding_ratio_lt

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution
    (hB : BiBalanced L) (v : Word A)
    (hrare : Tendsto
      (fun n : ℕ => (wordCount (avoidingLanguage L v) n : ℝ) / wordCount L n)
      atTop (𝓝 0)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ L,
      (∃ s ∈ followerFinset L u N, v <:+: s) ∧
      (∃ p ∈ predecessorFinset L u N, v <:+: p) := by
  obtain ⟨⟨cR, hcR, hR⟩, ⟨cP, hcP, hP⟩⟩ := hB
  have hc : (0 : ℝ) < min cR cP := lt_min hcR hcP
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (wordCount (avoidingLanguage L v) n : ℝ) / wordCount L n < min cR cP :=
    hrare.eventually (gt_mem_nhds hc)
  obtain ⟨N, hN, hsmallN⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  refine ⟨N, hN, uniform_occurrences_of_avoiding_ratio_lt ?_ ?_ hsmallN⟩
  · intro u hu
    exact (min_le_left _ _).trans (hR u hu N hN)
  · intro u hu
    exact (min_le_right _ _).trans (hP u hu N hN)
end BalanceSpecification
