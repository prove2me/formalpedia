-- Prove2me | solution 1 for CircuitLowerBound.Inf.Avail.mono
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:10:26.30957+00:00
-- url     : https://prove2.me/submissions/d8d21fdf-10ca-4f33-9a57-b7487539679c

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

private theorem wires_append (x : List Bool) (C D : Circuit) :
    wires x (C ++ D) = wires (wires x C) D := List.foldl_append

private theorem wires_concat (x : List Bool) (C : Circuit) (G : Gate) :
    wires x (C ++ [G]) =
      wires x C ++ [G.op ((wires x C).getD G.in₁ false) ((wires x C).getD G.in₂ false)] := by
  simp [wires]

private theorem length_wires (x : List Bool) (C : Circuit) :
    (wires x C).length = x.length + C.length := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih =>
    rw [wires_concat, List.length_append, ih, List.length_append]; simp; omega

private theorem prefix_wires (x : List Bool) (C : Circuit) : x <+: wires x C := by
  induction C using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton C G ih =>
    rw [wires_concat]; exact ih.trans (List.prefix_append _ _)

private theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem solution {n : ℕ} {C : Circuit} {g : List Bool → Bool}
    (h : Avail n C g) (D : Circuit) : Avail n (C ++ D) g := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, by rw [List.length_append]; omega, fun x hx => ?_⟩
  rw [wires_append, getD_of_prefix (prefix_wires _ D) (by rw [length_wires, hx]; exact hw), h x hx]
