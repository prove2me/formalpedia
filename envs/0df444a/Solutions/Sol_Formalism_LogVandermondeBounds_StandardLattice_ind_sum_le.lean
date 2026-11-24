-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.ind_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:51.214931+00:00
-- url     : https://prove2.me/submissions/9c07df7c-a885-45f3-811a-1a5e60b2baa7

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
theorem _root_.solution {N : ℕ} (a0 b0 : Fin N) (L : ℝ) (hL : 0 ≤ L) :
    ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (if a = a0 ∧ b = b0 then L else 0) ≤ L := by
  calc ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (if a = a0 ∧ b = b0 then L else 0)
      ≤ ∑ a : Fin N, (if a = a0 then L else 0) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases h : a = a0
        · simp only [h, true_and, if_true]
          rw [Finset.sum_ite_eq']
          split_ifs <;> linarith
        · simp [h]
    _ = L := by simp
end Formalism.LogVandermondeBounds.StandardLattice
