-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.len_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:43.900188+00:00
-- url     : https://prove2.me/submissions/2af4505d-7316-4d9d-81a3-6b55c69394ab

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu)
    (i : Fin n) : 0 ≤ len lam i := by
  unfold len
  have := h.2 i
  linarith [this.1, this.2]
end Formalism.LogVandermondeBounds.flipTwoThree
