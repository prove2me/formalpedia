-- Prove2me | solution 2 for ConsHalving.Additive.eq_1_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:19:38.656457+00:00
-- url     : https://prove2.me/submissions/71ae08ed-8add-4554-b6a9-3b3858e58158

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (x : Fin m → ℝ) :
    (∀ i, util u i x = util u i (fun j => 1 - x j)) ↔
      ∀ i, ∑ j, x j * u i j = (1 / 2) * ∑ j, u i j := by
  have key : ∀ i, util u i (fun j => 1 - x j) = ∑ j, u i j - ∑ j, x j * u i j := by
    intro i
    unfold util
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro h i
    have := h i
    rw [key i] at this
    unfold util at this
    linarith
  · intro h i
    rw [key i]
    unfold util
    have := h i
    linarith
