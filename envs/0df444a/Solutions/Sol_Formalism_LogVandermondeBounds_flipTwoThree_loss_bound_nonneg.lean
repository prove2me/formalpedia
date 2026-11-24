-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.loss_bound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:44.55182+00:00
-- url     : https://prove2.me/submissions/03aea556-06b9-4ba5-8d19-00b0bc3fd148

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
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    0 ≤ B0 lam nu := by
  unfold B0
  exact Finset.sum_nonneg (fun k _ => by have := (h.2 k).1; linarith)
end Formalism.LogVandermondeBounds.flipTwoThree
