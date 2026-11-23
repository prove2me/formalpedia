-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_fact_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:27.906051+00:00
-- url     : https://prove2.me/submissions/8a366d2d-de0a-4858-9fa9-822affa3da83

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (N : ℕ) : 0 < ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := by
  apply Finset.prod_pos
  intro i _
  exact Nat.cast_pos.mpr (Nat.factorial_pos i)
end Formalism.LogVandermondeBounds.StandardLattice
