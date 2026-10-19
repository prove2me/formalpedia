-- Prove2me | solution 1 for CohnElkies.normalizedProgram_le_normalizedCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/5b3d6a47-113b-4778-b4b0-6a39ff452f83

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedCostSet_bddBelow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (f : Admissible d) :
    normalizedProgram d ≤ normalizedCost f := by
  unfold normalizedProgram
  exact csInf_le (normalizedCostSet_bddBelow d) ⟨f, rfl⟩
end CohnElkies
