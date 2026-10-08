-- Prove2me | solution 1 for CJP83.CoverSeparation.configuration_inequality_valid
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:35:18.747014+00:00
-- url     : https://prove2.me/submissions/e0476103-8dd3-4de0-9d8b-828715c197ff

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
    (Sstar : Finset ι) (t : ι) (k r : ℕ)
    (hconfig : IsOneKConfiguration a a₀ Sstar t k)
    (hr₁ : k ≤ r) (hr₂ : r ≤ Sstar.card)
    (T x : Finset ι) (hT₁ : T ⊆ Sstar) (hT₂ : T.card = r)
    (hx : IsRowFeasible a a₀ x) :
    ((r : ℝ) - (k : ℝ) + 1) * binaryValue x t +
      ∑ j ∈ T, binaryValue x j ≤ (r : ℝ) := by
  rw [binary_sum]
  by_cases htx : t ∈ x
  · have hcard : (T ∩ x).card < k := by
      by_contra hnot
      have hkcard : k ≤ (T ∩ x).card := by omega
      rcases Finset.exists_subset_card_eq hkcard with ⟨Q, hQ, hQcard⟩
      have hQS : Q ⊆ Sstar := hQ.trans (Finset.inter_subset_left.trans hT₁)
      have hcov := hconfig.2.2.2.2 Q hQS hQcard
      exact cover_not_subset a a₀ hpos (insert t Q) x hcov hx
        (Finset.insert_subset_iff.mpr ⟨htx, hQ.trans Finset.inter_subset_right⟩)
    have hreal : ((T ∩ x).card : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hcard
    simp only [binaryValue, if_pos htx, mul_one]
    linarith
  · simp only [binaryValue, if_neg htx, mul_zero, zero_add]
    have hcard := Finset.card_le_card (Finset.inter_subset_left : T ∩ x ⊆ T)
    rw [hT₂] at hcard
    exact_mod_cast hcard
