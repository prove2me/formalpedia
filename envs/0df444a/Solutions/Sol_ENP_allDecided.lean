-- Prove2me | solution 1 for ENP.allDecided
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:36:39.329474+00:00
-- url     : https://prove2.me/submissions/e8148c5e-3b48-4c65-ba1e-3551b0f710a3

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_ext_of_dep
import Theorems.Thm_CircuitLowerBound_Inf_wires_concat

set_option autoImplicit false

open CircuitLowerBound.Inf
open ENP

theorem solution : ENP.AllDecided := by
  classical
  intro L n
  obtain ⟨D, w, -, hD⟩ :=
    ext_of_dep n le_rfl (fun x => decide (L x)) (fun x y hx hy h => by
      rw [List.take_of_length_le hx.le, List.take_of_length_le hy.le] at h; rw [h]) []
  refine ⟨_, [] ++ D ++ [⟨fun p _ => p, w, w⟩], le_rfl, fun x hx => ?_⟩
  rw [ENP.eval, wires_concat, List.getLastD_concat, hD x hx]
  simp
