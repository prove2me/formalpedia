-- Prove2me | solution 1 for CircuitLowerBound.Inf.Avail.gate
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:31:28.837266+00:00
-- url     : https://prove2.me/submissions/e542926a-85eb-44ec-aa13-858764b8d4bf

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
