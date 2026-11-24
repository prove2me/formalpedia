-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.norm_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:03.277219+00:00
-- url     : https://prove2.me/submissions/4d50c41c-3523-4df5-82ac-39a50c9cda20

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_pow_q_sq

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
theorem _root_.solution (hq : Fintype.card L = q ^ 2) (x : L) : (x ^ (q + 1)) ^ q = x ^ (q + 1) := by
  rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, pow_q_sq hq, ← pow_succ']
end Formalism.LogVandermondeBounds.StandardLattice
