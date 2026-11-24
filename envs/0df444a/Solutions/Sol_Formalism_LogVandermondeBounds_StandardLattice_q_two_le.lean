-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.q_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:43.874861+00:00
-- url     : https://prove2.me/submissions/e9458e96-1389-4ae0-a39c-31a4ca7a0103

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
theorem _root_.solution (hq : Fintype.card L = q ^ 2) : 2 ≤ q := by
  have h := Fintype.one_lt_card (α := L)
  rw [hq] at h
  by_contra h'
  push Not at h'
  interval_cases q <;> simp at h
end Formalism.LogVandermondeBounds.StandardLattice
