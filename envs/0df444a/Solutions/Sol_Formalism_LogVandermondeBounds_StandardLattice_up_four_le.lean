-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_four_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:44.529669+00:00
-- url     : https://prove2.me/submissions/959d8018-2eb1-498a-bb13-15b9d5d23be2

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds

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
theorem _root_.solution (n t : ℕ) (ht : 1 ≤ t) : (4 : ℝ) ≤ ((n : ℝ) + 2) * ((t : ℝ) + t) := by
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith
end Formalism.LogVandermondeBounds.StandardLattice
