-- Prove2me | solution 1 for CJP83.CoverSeparation.violated_cover_iff_knapsack_value_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:37:59.043809+00:00
-- url     : https://prove2.me/submissions/b378e43b-679b-4204-8f6d-537396fbd528

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

open CJP83.CoverSeparation
open scoped BigOperators

theorem violated_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z)
    (S : Finset ι) (hcover : IsMinimalCover a a₀ S)
    (hviolated : (S.card : ℝ) - 1 < ∑ j ∈ S, xbar j) : z < 1 := by
  have hzle := hz.2 (show (∑ j ∈ S, (1 - xbar j)) ∈ sepValues a a₀ xbar from
    ⟨S, hcover.1, rfl⟩)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hzle
  linarith

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

theorem optimal_minimal_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (hcube : ∀ j, 0 ≤ xbar j ∧ xbar j ≤ 1)
    (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z) :
    (∃ S : Finset ι, IsMinimalCover a a₀ S ∧
      (S.card : ℝ) - 1 < ∑ j ∈ S, xbar j) ↔ z < 1 := by
  constructor
  · rintro ⟨S, hS, hviolated⟩
    exact violated_aux a a₀ hpos xbar z hz S hS hviolated
  · intro hz1
    rcases optimal_minimal_aux a a₀ hpos xbar hcube z hz with ⟨S, hS, heq⟩
    refine ⟨S, hS, ?_⟩
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at heq
    linarith
