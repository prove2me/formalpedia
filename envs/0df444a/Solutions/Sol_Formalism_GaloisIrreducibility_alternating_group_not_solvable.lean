-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.alternating_group_not_solvable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:20.74252+00:00
-- url     : https://prove2.me/submissions/2f5e2156-f0a0-4dea-954d-d9e18c86f73d

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_AltNotSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : AltNotSolvable := by
  intro α _ _ h hA
  have hcard : 5 ≤ Cardinal.mk α := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast h
  refine Equiv.Perm.not_isSolvable α hcard ?_
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)
end Formalism.GaloisIrreducibility
