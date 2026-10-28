-- Prove2me | solution 2 for FlowJobShop.PartitionFlow.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:15.457478+00:00
-- url     : https://prove2.me/submissions/4f857099-dad3-43ed-87cf-d330abc1363b

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop
import Definitions.Def_FlowJobShop_PartitionFlow_Partition
import Definitions.Def_FlowJobShop_PartitionFlow_Instance
import Theorems.Thm_FlowJobShop_PartitionFlow_lemma_1a
import Theorems.Thm_FlowJobShop_PartitionFlow_lemma_1b

-- carved verbatim out of submission 507f0238-f5f7-4f63-9a99-bb828e1af430, lines 545-551

section
open FlowJobShop.PartitionFlow.FlowShop
open FlowJobShop
open FlowJobShop.PartitionFlow
open MeasureTheory

theorem lemma_1_core {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a := by
  constructor
  · rintro ⟨S, hS⟩
    by_contra h
    have := FlowJobShop.PartitionFlow.lemma_1b a h S
    linarith
  · intro h
    obtain ⟨S, _, he⟩ := FlowJobShop.PartitionFlow.lemma_1a a h
    exact ⟨S, he.le⟩

theorem corollary_1_core {n : ℕ} (a : Fin n → ℕ) :
    (∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
      HasPartition a := by
  constructor
  · rintro ⟨S, _, hS⟩
    by_contra h
    have := FlowJobShop.PartitionFlow.lemma_1b a h S
    linarith
  · intro h
    obtain ⟨S, hn, he⟩ := FlowJobShop.PartitionFlow.lemma_1a a h
    exact ⟨S, hn, he.le⟩

theorem atMostTwo_core {n : ℕ} (a : Fin n → ℕ) : (FS a).AtMostTwoNonzeroTasks := by
  intro i
  rcases i with i | k
  · have : (Finset.univ : Finset (Fin 3)).filter (fun j => (FS a).t j (Sum.inl i) ≠ 0)
        ⊆ ({0, 2} : Finset (Fin 3)) := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      fin_cases j <;> simp [FS, fsTimes] at hj ⊢
    exact (Finset.card_le_card this).trans Finset.card_le_two
  · fin_cases k
    · have : (Finset.univ : Finset (Fin 3)).filter (fun j => (FS a).t j (Sum.inr 0) ≠ 0)
          ⊆ ({0, 1} : Finset (Fin 3)) := by
        intro j hj
        simp only [Finset.mem_filter] at hj
        fin_cases j <;> simp [FS, fsTimes] at hj ⊢
      exact (Finset.card_le_card this).trans Finset.card_le_two
    · have : (Finset.univ : Finset (Fin 3)).filter (fun j => (FS a).t j (Sum.inr 1) ≠ 0)
          ⊆ ({1, 2} : Finset (Fin 3)) := by
        intro j hj
        simp only [Finset.mem_filter] at hj
        fin_cases j <;> simp [FS, fsTimes] at hj ⊢
      exact (Finset.card_le_card this).trans Finset.card_le_two

end

section
open FlowJobShop.PartitionFlow.FlowShop
open FlowJobShop.PartitionFlow

theorem solution {n : ℕ} (a : Fin n → ℕ) :
    (FS a).AtMostTwoNonzeroTasks ∧
      ((∃ S : PreemptiveSchedule (FS a), S.finishTime ≤ 2 * T a) ↔ HasPartition a) ∧
      ((∃ S : PreemptiveSchedule (FS a), S.IsNonPreemptive ∧ S.finishTime ≤ 2 * T a) ↔
        HasPartition a) := by
  exact ⟨atMostTwo_core a, lemma_1_core a, corollary_1_core a⟩

end
