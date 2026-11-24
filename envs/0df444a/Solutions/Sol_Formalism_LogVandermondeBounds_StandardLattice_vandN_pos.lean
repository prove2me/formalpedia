-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.vandN_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:50.50265+00:00
-- url     : https://prove2.me/submissions/4dbdaf79-2a0c-4ba0-be65-d6cec1f934c2

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
theorem _root_.solution (x : ℕ → ℝ) (N : ℕ) (h : ∀ i j, i < j → j < N → x j < x i) : 0 < vandN x N := by
  unfold vandN
  apply prod_pos
  intro i hi
  apply prod_pos
  intro j hj
  rw [mem_range] at hi
  rw [mem_Ico] at hj
  exact sub_pos.2 (h i j (by omega) (by omega))
end Formalism.LogVandermondeBounds.StandardLattice
