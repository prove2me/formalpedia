-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.cardUnitriangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:27.267009+00:00
-- url     : https://prove2.me/submissions/c8a1e7ae-0ff2-42d8-9593-ba08c5f3a089

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_card_lt_pairs

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
theorem _root_.solution : CardUnitriangular := by
  intro F _ _ _ n
  rw [Nat.card_congr (upperEquiv F n)]
  rw [Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]
end Formalism.LogVandermondeBounds.StandardLattice
