-- Prove2me | solution 1 for CapacityGames.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:47:10.942858+00:00
-- url     : https://prove2.me/submissions/863e585e-e061-4632-b4b4-511942975ac6

import Mathlib
import Definitions.Def_CapacityGames_SetFunction

open CapacityGames in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] (f : Finset N → ℝ)
    (hf : CapacityGames.LocalSubmodular f) (i : N) :
    (CapacityGames.contribSet f).erase i ⊆ CapacityGames.contribSetExcept f i := by
  intro j hj
  rw [Finset.mem_erase] at hj
  obtain ⟨hji, hjU⟩ := hj
  simp only [CapacityGames.contribSet, CapacityGames.contribSetExcept, Finset.mem_filter,
    Finset.mem_univ, true_and] at hjU ⊢
  have := hf Finset.univ j (Finset.mem_univ _) i (Finset.mem_univ _) hji
  rw [Finset.erase_right_comm] at this
  linarith
