-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.dist_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:42.255805+00:00
-- url     : https://prove2.me/submissions/5a21c614-bdcb-496b-9554-d4cc4eafb69c

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded

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
theorem _root_.solution {N : ℕ} (a b : Fin N) (h : a < b) :
    ((b.val - a.val - 1 : ℕ) : ℝ) + 1 = (b.val : ℝ) - a.val := by
  have h' : a.val < b.val := h
  have : b.val - a.val - 1 + 1 + a.val = b.val := by omega
  have h2 : (((b.val - a.val - 1 : ℕ) : ℝ) + 1) + (a.val : ℝ) = b.val := by exact_mod_cast this
  linarith
end Formalism.LogVandermondeBounds.StandardLattice
