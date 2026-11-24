-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.vandN_succ_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:40.63826+00:00
-- url     : https://prove2.me/submissions/f14165cb-5e2e-4f5d-8b1f-175766eeb337

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_VandNSuccRight

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
theorem _root_.solution (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = vandN x N * ∏ i ∈ range N, (x i - x N) := by
  unfold vandN
  rw [prod_range_succ, Ico_self, prod_empty, mul_one, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [prod_Ico_succ_top (by omega : i + 1 ≤ N)]
end Formalism.LogVandermondeBounds.StandardLattice
