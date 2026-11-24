-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_fact_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:43.896822+00:00
-- url     : https://prove2.me/submissions/a07a1bd0-638c-4a36-bf1c-b415f7fbccc5

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
private theorem one_le_mul_of_one_le_of_one_le' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith
end Formalism.LogVandermondeBounds.StandardLattice
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (N : ℕ) : 1 ≤ ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ]
    have h0 : 1 ≤ N.factorial := Nat.factorial_pos N
    have h1 : (1 : ℝ) ≤ ((N.factorial : ℕ) : ℝ) := by exact_mod_cast h0
    exact one_le_mul_of_one_le_of_one_le' ih h1
end Formalism.LogVandermondeBounds.StandardLattice
