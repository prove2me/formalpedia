-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.harm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:48.765008+00:00
-- url     : https://prove2.me/submissions/e53a24ae-0af1-497d-94b6-dc1280fbc27c

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
theorem _root_.solution (N : ℕ) : ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add,
    Nat.cast_one] at this
  simpa [one_div] using this
end Formalism.LogVandermondeBounds.StandardLattice
