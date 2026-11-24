-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.up_vandN_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:47.690206+00:00
-- url     : https://prove2.me/submissions/c586d7e4-3e1b-413a-9f39-cb46395baf8c

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
theorem _root_.solution (x : ℕ → ℝ) (N : ℕ) (h : ∀ i j, i < j → j < N → x j < x i) :
    0 < vandN x N := by
  unfold vandN
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Ico] at hj
  have := h i j (by omega) hj.2
  linarith
end Formalism.LogVandermondeBounds.StandardLattice
