-- Prove2me | solution 1 for BudgetClock.Monotone.benchmark_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T08:42:47.647499+00:00
-- url     : https://prove2.me/submissions/0687ede6-e850-42c2-b49f-0ca93064d5ec

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

open BudgetClock.Monotone in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      ∃ Q : Finset (Fin n),
        Q ⊆ Finset.univ \ ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) ∧
        ∑ i ∈ Q, c i ≤ B ∧
        v O ≤ v ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) +
          marg v Q ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) := by
  intro O hO
  set W := (W1 v c B).toFinset ∪ (W2bar v c B).toFinset
  refine ⟨O \ W, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  · exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _ => hc i)) hO
  · unfold marg
    rw [Finset.union_sdiff_self_eq_union]
    have := hmono O (W ∪ O) Finset.subset_union_right
    linarith
