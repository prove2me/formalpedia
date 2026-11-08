-- Prove2me | solution 1 for CapacityGames.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:32:04.713981+00:00
-- url     : https://prove2.me/submissions/c002c6f2-6c76-47c8-90fa-26dc5158cb00

import Mathlib
import Definitions.Def_CapacityGames_SetFunction

open CapacityGames in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] (f : Finset N → ℝ) (hf : LocalSubmodular f)
    (S : Finset N) :
    ∑ i ∈ Finset.univ \ S, (f Finset.univ - f (Finset.univ.erase i)) ≤ f Finset.univ - f S := by
  have hA : ∀ (i : N) (R : Finset N), i ∉ R →
      f Finset.univ - f (Finset.univ.erase i) ≤
        f (Finset.univ \ R) - f ((Finset.univ \ R).erase i) := by
    intro i R
    induction R using Finset.induction_on with
    | empty => intro _; simp
    | insert j R' hj ih =>
      intro hi
      have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      have hiR : i ∉ R' := fun h => hi (Finset.mem_insert_of_mem h)
      have h1 := ih hiR
      have hiT : i ∈ Finset.univ \ R' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiR⟩
      have hjT : j ∈ Finset.univ \ R' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
      have h2 := hf (Finset.univ \ R') i hiT j hjT hij
      rw [Finset.sdiff_insert, Finset.erase_right_comm]
      linarith
  have hB : ∀ R : Finset N, ∑ i ∈ R, (f Finset.univ - f (Finset.univ.erase i)) ≤
      f Finset.univ - f (Finset.univ \ R) := by
    intro R
    induction R using Finset.induction_on with
    | empty => simp
    | insert j R' hj ih =>
      rw [Finset.sum_insert hj, Finset.sdiff_insert]
      have := hA j R' hj
      linarith
  have := hB (Finset.univ \ S)
  rwa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)] at this
