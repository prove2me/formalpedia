-- Prove2me | solution 1 for Formalism.SLP.P.eq_zmultiples_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:22.567268+00:00
-- url     : https://prove2.me/submissions/3be8a884-3627-4207-85cb-c7f2a6b85a7d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup
namespace Formalism.SLP.P
theorem _root_.solution (D : AddSubgroup ℤ) : D = zmultiples (D.index : ℤ) := by
  obtain ⟨a, rfl⟩ := Int.subgroup_cyclic D
  rw [← zmultiples_eq_closure, Int.index_zmultiples, Int.zmultiples_natAbs]
end Formalism.SLP.P
