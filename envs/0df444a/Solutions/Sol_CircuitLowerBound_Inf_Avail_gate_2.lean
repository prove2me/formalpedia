-- Prove2me | solution 2 for CircuitLowerBound.Inf.Avail.gate
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:41:02.426596+00:00
-- url     : https://prove2.me/submissions/b7ab3d2e-eb07-4377-8d7b-602d0a4a8dc6

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_wires_concat
import Theorems.Thm_CircuitLowerBound_Inf_length_wires

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem solution {n : ℕ} {C : Circuit} {g₁ g₂ : List Bool → Bool}
    (h₁ : Avail n C g₁) (h₂ : Avail n C g₂) (op : Bool → Bool → Bool) :
    ∃ G : Gate, Avail n (C ++ [G]) fun x => op (g₁ x) (g₂ x) := by
  obtain ⟨w₁, -, h₁⟩ := h₁
  obtain ⟨w₂, -, h₂⟩ := h₂
  refine ⟨⟨op, w₁, w₂⟩, n + C.length, by simp, fun x hx => ?_⟩
  rw [wires_concat, List.getD_append_right _ _ _ _ (by rw [length_wires, hx]),
    length_wires, hx, h₁ x hx, h₂ x hx]
  simp
