-- Prove2me | solution 1 for BudgetAgg.NashChar.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:50:37.783194+00:00
-- url     : https://prove2.me/submissions/51c90c89-b48a-46ef-adae-01fe3880f29b

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_6
import Theorems.Thm_BudgetAgg_NashChar_lemma_3

open BudgetAgg.NashChar

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hnash : IsNashOutcome P q.1) : IsCoreFairShare P q := by
  obtain ⟨s, ⟨hs0, hscol, hsrow⟩, hsupp⟩ := (lemma_6 P q).1 hnash
  apply lemma_3 P q
  intro G
  have h1 : ∀ i ∈ G, ∑ j ∈ critG P q.1 G, s i j = 1 / (n : ℝ) := by
    intro i hi
    rw [← hsrow i]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply hsupp
    intro hjc
    apply hj
    exact Finset.mem_biUnion.mpr ⟨i, hi, hjc⟩
  calc (G.card : ℝ) / (n : ℝ) = ∑ i ∈ G, ∑ j ∈ critG P q.1 G, s i j := by
        rw [Finset.sum_congr rfl h1]; simp [div_eq_mul_inv]
    _ = ∑ j ∈ critG P q.1 G, ∑ i ∈ G, s i j := Finset.sum_comm
    _ ≤ ∑ j ∈ critG P q.1 G, ∑ i, s i j := by
        apply Finset.sum_le_sum
        intro j _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => hs0 i j)
    _ = ∑ j ∈ critG P q.1 G, q.1 j := by
        apply Finset.sum_congr rfl; intro j _; exact hscol j

