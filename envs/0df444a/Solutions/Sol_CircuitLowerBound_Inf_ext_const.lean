-- Prove2me | solution 1 for CircuitLowerBound.Inf.ext_const
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:18:44.854748+00:00
-- url     : https://prove2.me/submissions/14a573e1-f67d-419a-929d-152d0a0902ae

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_wires_append
import Theorems.Thm_CircuitLowerBound_Inf_prefix_wires

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

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

theorem solution (n : ℕ) (b : Bool) : Ext n fun _ => b := fun C₀ =>
  ⟨[⟨fun _ _ => b, 0, 0⟩], n + C₀.length, by simp, fun x hx => by
    rw [wires_concat, List.getD_append_right _ _ _ _ (by rw [length_wires, hx]), length_wires, hx]
    simp⟩
