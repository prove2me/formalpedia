-- Prove2me | solution 1 for CompDesignBFM.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:28:06.328706+00:00
-- url     : https://prove2.me/submissions/46e31e8f-ec9c-4721-a8bc-99c442c7f4f0

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF

open CompDesignBFM

lemma sb_aux {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0)
    (hs : IsSubmodularSF v) (S : Finset (Fin n)) :
    ∑ i ∈ S, (v S - v (S.erase i)) ≤ v S := by
  induction S using Finset.induction_on with
  | empty => simp [hv0]
  | insert a S0 ha ih =>
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have hle : ∑ i ∈ S0, (v (insert a S0) - v ((insert a S0).erase i)) ≤
        ∑ i ∈ S0, (v S0 - v (S0.erase i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have herase : (insert a S0).erase i = insert a (S0.erase i) :=
        Finset.erase_insert_of_ne (Ne.symm hia)
      have hsub : S0.erase i ⊆ insert a (S0.erase i) := Finset.subset_insert a _
      have hnot : i ∉ insert a (S0.erase i) := by
        simp [hia]
      have := hs (S0.erase i) (insert a (S0.erase i)) i hsub hnot
      have e1 : insert i (insert a (S0.erase i)) = insert a S0 := by
        rw [Finset.insert_comm, Finset.insert_erase hi]
      have e2 : insert i (S0.erase i) = S0 := Finset.insert_erase hi
      rw [e1, e2] at this
      rw [herase]
      linarith
    linarith

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hm : IsMonotoneSF v)
    (hs : IsSubmodularSF v) (S : Finset (Fin n)) :
    ∑ i ∈ S, (v S - v (S.erase i)) ≤ v S := sb_aux v hv0 hs S
