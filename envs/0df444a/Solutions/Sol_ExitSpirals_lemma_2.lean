-- Prove2me | solution 1 for ExitSpirals.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:45:13.831664+00:00
-- url     : https://prove2.me/submissions/a739ff24-ff51-49ae-8cae-c02bba15d9d7

import Mathlib
import Definitions.Def_ExitSpirals_Network
import Definitions.Def_ExitSpirals_IsMutuallyStable
import Definitions.Def_ExitSpirals_activity

open ExitSpirals in
theorem solution {n : ℕ} (ER EC : ExitSpirals.Network n) (hR : ExitSpirals.IsLoopless ER)
    (hC : ExitSpirals.IsLoopless EC)
    (h43R : ∀ i, 0 < ExitSpirals.inDeg ER i) (h43C : ∀ i, 0 < ExitSpirals.inDeg EC i) :
    ExitSpirals.maxEq ER EC ∅ = Finset.univ ∧ ExitSpirals.IsMutuallyStable ER EC Finset.univ := by
  have hin : ∀ E : ExitSpirals.Network n, (∀ i, 0 < ExitSpirals.inDeg E i) →
      ∀ i, ∃ j, (j, i) ∈ E := by
    intro E h i
    obtain ⟨e, he⟩ := Finset.card_pos.1 (h i)
    rw [Finset.mem_filter] at he
    exact ⟨e.1, by rw [← he.2]; exact he.1⟩
  have hEq : ExitSpirals.IsEquilibrium ER EC ∅ Finset.univ := by
    unfold ExitSpirals.IsEquilibrium
    ext i
    simp only [ExitSpirals.bestResponse, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, not_false_eq_true, iff_true]
    obtain ⟨j, hj⟩ := hin ER h43R i
    obtain ⟨j', hj'⟩ := hin EC h43C i
    exact ⟨⟨j, hj⟩, ⟨j', hj'⟩⟩
  refine ⟨?_, ⟨fun i _ => ?_, fun i _ => ?_⟩⟩
  · ext i
    simp only [ExitSpirals.maxEq, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨_, hEq, Finset.mem_univ i⟩
  · obtain ⟨j, hj⟩ := hin ER h43R i
    exact ⟨j, Finset.mem_univ _, hj⟩
  · obtain ⟨j, hj⟩ := hin EC h43C i
    exact ⟨j, Finset.mem_univ _, hj⟩
