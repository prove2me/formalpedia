-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.half_add_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:30.762838+00:00
-- url     : https://prove2.me/submissions/c9009a99-411f-4774-bc9c-c10c0043dbdd

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector

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
theorem _root_.solution (n : ℕ) : n * (n - 1) / 2 + n * (n + 1) / 2 = n * n := by
  rcases n with _ | k
  · simp
  · obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    have h1 : (k + 1) * k = m + m := by rw [mul_comm]; exact hm
    have h2 : (k + 1) * (k + 1 + 1) = m + m + 2 * (k + 1) := by rw [← h1]; ring
    have h3 : (k + 1) * (k + 1) = m + m + (k + 1) := by rw [← h1]; ring
    rw [Nat.add_sub_cancel, h1, h2, h3]
    omega
end Formalism.LogVandermondeBounds.StandardLattice
