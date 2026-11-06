-- Prove2me | solution 2 for CircuitLowerBound.Inf.Ext.congr
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:10:25.697439+00:00
-- url     : https://prove2.me/submissions/7c11b6ef-e0ad-49df-a4ad-b86a958aa44e

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf

set_option autoImplicit false

open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem solution {n : ℕ} {g g' : List Bool → Bool} (h : Ext n g)
    (e : ∀ x : List Bool, x.length = n → g x = g' x) : Ext n g' := fun C₀ => by
  obtain ⟨D, w, hw, hD⟩ := h C₀
  exact ⟨D, w, hw, fun x hx => (hD x hx).trans (e x hx)⟩
