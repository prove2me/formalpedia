-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.prodFactorialShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:20:39.593974+00:00
-- url     : https://prove2.me/submissions/db1c53ee-e3de-4d0d-addf-6c2a5c6637a2

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities

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
theorem _root_.solution : ProdFactorialShift := by
  intro k r hkr
  induction r, hkr using Nat.le_induction with
  | base => simp
  | succ r hkr ih =>
    rw [Finset.prod_Ico_succ_top (by omega : k + 1 ≤ r + 1), Finset.prod_range_succ, ← ih]
    simp only [Nat.add_sub_cancel]
    ring
end Formalism.LogVandermondeBounds.StandardLattice
