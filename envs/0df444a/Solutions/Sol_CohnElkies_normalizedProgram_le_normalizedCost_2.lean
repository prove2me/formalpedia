-- Prove2me | solution 2 for CohnElkies.normalizedProgram_le_normalizedCost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:05.350269+00:00
-- url     : https://prove2.me/submissions/7b64082a-51e3-4f44-a5d2-4965d2f82b25

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution {d : ℕ}
    (f : Admissible d) :
    normalizedProgram d ≤ normalizedCost f := by
  refine csInf_le ⟨0, ?_⟩ ⟨f, rfl⟩
  rintro x ⟨g, rfl⟩
  unfold normalizedCost quotient
  have := (div_pos (admissible_zero_pos g) g.fourier_zero_pos).le
  positivity

