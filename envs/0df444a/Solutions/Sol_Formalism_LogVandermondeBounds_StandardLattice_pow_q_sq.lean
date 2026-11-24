-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.pow_q_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:43.180798+00:00
-- url     : https://prove2.me/submissions/3e07e047-e510-4d93-b2ac-e99fcd25450e

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound

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
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (hq : Fintype.card L = q ^ 2) (x : L) : x ^ (q ^ 2) = x := by
  rw [← hq]; exact FiniteField.pow_card x
end Formalism.LogVandermondeBounds.StandardLattice
