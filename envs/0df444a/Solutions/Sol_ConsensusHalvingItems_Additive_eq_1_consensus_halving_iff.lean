-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.eq_1_consensus_halving_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:35:45.843874+00:00
-- url     : https://prove2.me/submissions/317c74ef-94fe-44f7-9787-01ee3b6d1d01

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving

open ConsensusHalvingItems.Additive in
theorem solution {n m : ℕ} (u : Fin n → Fin m → ℚ) (x : Fin m → ℚ)
    (hx : IsFractionalSet x) :
    IsConsensusHalving u x ↔ ∀ i, ∑ j, x j * u i j = 1 / 2 * ∑ j, u i j := by
  constructor
  · rintro ⟨_, h⟩ i
    have := h i
    unfold additiveUtil at this
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib] at this
    linarith
  · intro h
    refine ⟨hx, fun i => ?_⟩
    unfold additiveUtil
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
    linarith [h i]
