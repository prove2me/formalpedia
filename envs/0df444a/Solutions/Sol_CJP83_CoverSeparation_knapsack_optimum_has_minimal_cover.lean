-- Prove2me | solution 1 for CJP83.CoverSeparation.knapsack_optimum_has_minimal_cover
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:35:22.316983+00:00
-- url     : https://prove2.me/submissions/90744259-e238-4522-8da8-40401baa5669

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

open CJP83.CoverSeparation
open scoped BigOperators

private lemma minimal_subcover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (s : Finset ι) (hs : a₀ < ∑ j ∈ s, a j) :
    ∃ S : Finset ι, S ⊆ s ∧ IsMinimalCover a a₀ S := by
  revert hs
  refine Finset.strongInductionOn s ?_
  intro s ih hs
  by_cases hminimal : ∀ k ∈ s, (∑ j ∈ s, a j) - a k ≤ a₀
  · exact ⟨s, Finset.Subset.refl _, hs, hminimal⟩
  · push Not at hminimal
    rcases hminimal with ⟨k, hk, hlarge⟩
    have hsmall : a₀ < ∑ j ∈ s.erase k, a j := by
      rw [Finset.sum_erase_eq_sub hk]
      exact hlarge
    rcases ih (s.erase k) (Finset.erase_ssubset hk) hsmall with ⟨S, hSs, hS⟩
    exact ⟨S, hSs.trans (Finset.erase_subset _ _), hS⟩

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (hcube : ∀ j, 0 ≤ xbar j ∧ xbar j ≤ 1)
    (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z) :
    ∃ S : Finset ι, IsMinimalCover a a₀ S ∧ (∑ j ∈ S, (1 - xbar j)) = z := by
  rcases hz.1 with ⟨s, hs, hsz⟩
  rcases minimal_subcover a a₀ s hs with ⟨S, hSs, hS⟩
  refine ⟨S, hS, le_antisymm ?_ ?_⟩
  · rw [hsz]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSs (fun j _ _ => sub_nonneg.mpr (hcube j).2)
  · exact hz.2 ⟨S, hS.1, rfl⟩
