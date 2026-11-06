-- Prove2me | solution 1 for CircuitLowerBound.Inf.Ext.op
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:31:28.303737+00:00
-- url     : https://prove2.me/submissions/893934b8-764f-45b9-b3a8-84b10977794b

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_Avail_mono
import Theorems.Thm_CircuitLowerBound_Inf_wires_concat
import Theorems.Thm_CircuitLowerBound_Inf_length_wires

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

private theorem Avail_gate' {n : ℕ} {C : Circuit} {g₁ g₂ : List Bool → Bool}
    (h₁ : Avail n C g₁) (h₂ : Avail n C g₂) (op : Bool → Bool → Bool) :
    ∃ G : Gate, Avail n (C ++ [G]) fun x => op (g₁ x) (g₂ x) := by
  obtain ⟨w₁, -, h₁⟩ := h₁
  obtain ⟨w₂, -, h₂⟩ := h₂
  refine ⟨⟨op, w₁, w₂⟩, n + C.length, by simp, fun x hx => ?_⟩
  rw [wires_concat, List.getD_append_right _ _ _ _ (by rw [length_wires, hx]),
    length_wires, hx, h₁ x hx, h₂ x hx]
  simp

theorem solution {n : ℕ} {g₁ g₂ : List Bool → Bool}
    (h₁ : Ext n g₁) (h₂ : Ext n g₂) (gateFn : Bool → Bool → Bool) :
    Ext n fun x => gateFn (g₁ x) (g₂ x) := fun C₀ => by
  obtain ⟨D₁, a₁⟩ := h₁ C₀
  obtain ⟨D₂, a₂⟩ := h₂ (C₀ ++ D₁)
  obtain ⟨G, a⟩ := Avail_gate' (Avail.mono a₁ D₂) a₂ gateFn
  exact ⟨D₁ ++ D₂ ++ [G], by simpa only [List.append_assoc] using a⟩
