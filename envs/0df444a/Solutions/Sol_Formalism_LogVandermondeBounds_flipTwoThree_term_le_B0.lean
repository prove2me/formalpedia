-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.term_le_B0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:45.957329+00:00
-- url     : https://prove2.me/submissions/40217f2a-9ba9-4823-be61-7b95f2199b17

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
    (i : Fin n) : nu i - lam i.succ ≤ B0 lam nu := by
  unfold B0
  exact Finset.single_le_sum (f := fun k => nu k - lam k.succ)
    (fun k _ => by have := (h.2 k).1; linarith) (Finset.mem_univ i)
end Formalism.LogVandermondeBounds.flipTwoThree
