-- Prove2me | solution 1 for CJP83.CoverSeparation.cover_inequality_valid
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:35:17.236522+00:00
-- url     : https://prove2.me/submissions/f6e42ba2-e920-4d99-b7f7-7112c170ef53

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

open CJP83.CoverSeparation
open scoped BigOperators

private lemma cover_not_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (S x : Finset ι) (hcover : IsMinimalCover a a₀ S)
    (hx : IsRowFeasible a a₀ x) : ¬ S ⊆ x := by
  intro hsub
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => (hpos j).le)
  exact (not_lt_of_ge (hle.trans hx)) hcover.1

private lemma binary_sum {ι : Type*} [DecidableEq ι] (S x : Finset ι) :
    (∑ j ∈ S, binaryValue x j) = ((S ∩ x).card : ℝ) := by
  simp [binaryValue]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (S x : Finset ι) (hcover : IsMinimalCover a a₀ S)
    (hx : IsRowFeasible a a₀ x) :
    (∑ j ∈ S, binaryValue x j) ≤ (S.card : ℝ) - 1 := by
  rw [binary_sum]
  have hproper : S ∩ x ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    exact cover_not_subset a a₀ hpos S x hcover hx
      (heq ▸ Finset.inter_subset_right)
  have hcard := Finset.card_lt_card hproper
  have hreal : ((S ∩ x).card : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hcard
  linarith
