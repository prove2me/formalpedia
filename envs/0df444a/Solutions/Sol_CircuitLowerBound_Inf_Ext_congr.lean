-- Prove2me | solution 1 for CircuitLowerBound.Inf.Ext.congr
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:10:25.287198+00:00
-- url     : https://prove2.me/submissions/d7e2ecc3-bbcd-42ac-8af4-48241734221b

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
