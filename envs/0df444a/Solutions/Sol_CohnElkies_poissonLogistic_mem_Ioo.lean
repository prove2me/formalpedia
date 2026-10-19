-- Prove2me | solution 1 for CohnElkies.poissonLogistic_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/4a3276c4-1d28-4177-bbb5-3fe1c378659c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_image_univ

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    poissonLogistic u ∈ Ioo (0 : ℝ) 1 := by
  rw [← poissonLogistic_image_univ]
  exact ⟨u, Set.mem_univ _, rfl⟩
end CohnElkies
