-- Prove2me | solution 1 for Everyday.invariant_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:24:02.05096+00:00
-- url     : https://prove2.me/submissions/858fa76f-dbd7-47b8-b35b-d21c8b8c5058

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open scoped BigOperators

open Everyday
/-- Spacetime: the invariant volume of the everyday world is positive —
the measure √(-g) d⁴x assigns positive volume, and a nonempty discrete
spacetime with positive volume weights has positive total volume. -/


theorem solution {X : Type} [Fintype X] [Nonempty X] (vol : X → ℝ)
    (h : ∀ x, 0 < vol x) : 0 < ∑ x, vol x := by
  exact Finset.sum_pos (fun x _ => h x) Finset.univ_nonempty


