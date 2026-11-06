-- Prove2me | solution 1 for CircuitLowerBound.Inf.ext_proj
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:18:45.276995+00:00
-- url     : https://prove2.me/submissions/599c1cf0-350d-4531-a7b0-7fd1966b518a

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_prefix_wires

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

private theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem solution {n i : ℕ} (hi : i < n) : Ext n fun x => x.getD i false := fun C₀ =>
  ⟨[], i, by omega, fun x hx => by
    rw [List.append_nil]
    exact getD_of_prefix (prefix_wires x C₀) (by omega)⟩
