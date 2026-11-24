-- Prove2me | solution 1 for Formalism.G0.TopsCount.binLower_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:24.978216+00:00
-- url     : https://prove2.me/submissions/b020d360-08db-4567-8de2-5a82cf9bbe4e

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
import Theorems.Thm_Formalism_G0_TopsCount_A_succ
import Theorems.Thm_Formalism_G0_TopsCount_pascal_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsCount
namespace Formalism.G0.TopsCount
theorem _root_.solution (m : ℕ) (δ : ℝ) (N : ℕ) :
    binLower (m + 1) δ N = (1 - δ) * A m δ N + δ * A m δ (N - 1) := by
  induction N with
  | zero => simp [binLower, A]
  | succ N ih =>
    have hs : binLower (m + 1) δ (N + 1) =
        binLower (m + 1) δ N + ((m + 1).choose N : ℝ) * δ ^ N * (1 - δ) ^ (m + 1 - N) := by
      unfold binLower; rw [sum_range_succ]
    rw [hs, ih]
    cases N with
    | zero =>
      simp [A, a]
      ring
    | succ k =>
      rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega,
        A_succ m δ (k + 1), A_succ m δ k, pascal_term]
      ring
end Formalism.G0.TopsCount
