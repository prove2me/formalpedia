-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.sum_log_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:45.28346+00:00
-- url     : https://prove2.me/submissions/fe5a5932-a1ba-45d1-aeb2-cd5c7c12ae90

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap

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
theorem _root_.solution (k r : ℕ) (hkr : k ≤ r) :
    ∑ M ∈ Ico (k + 1) (r + 1), Real.log (((M - 1).factorial : ℕ) : ℝ)
      + ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ)
      = ∑ i ∈ range r, Real.log ((i.factorial : ℕ) : ℝ) := by
  induction r, hkr using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (by omega : k + 1 ≤ n + 1), Finset.sum_range_succ, ← ih]
    simp only [Nat.add_sub_cancel]
    ring
end Formalism.LogVandermondeBounds.StandardLattice
