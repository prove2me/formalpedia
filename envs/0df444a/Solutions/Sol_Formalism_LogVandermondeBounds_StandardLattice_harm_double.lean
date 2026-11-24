-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.harm_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:01.598273+00:00
-- url     : https://prove2.me/submissions/ece24705-315b-4d8a-8066-52bb3d201e2a

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_inner_harm_le
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_harm_le

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
theorem _root_.solution (N : ℕ) :
    ∑ a : Fin N, ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) ≤
      2 * N * (1 + Real.log N) := by
  calc ∑ a : Fin N, ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1)
      ≤ ∑ a : Fin N, 2 * (1 + Real.log N) := by
        apply Finset.sum_le_sum
        intro a _
        have h := (inner_harm_le a).trans (harm_le N)
        have e : ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) =
            2 * ∑ b ∈ univ.filter (fun b => a < b), 1 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
        rw [e]; linarith
    _ = 2 * N * (1 + Real.log N) := by simp; ring
end Formalism.LogVandermondeBounds.StandardLattice
