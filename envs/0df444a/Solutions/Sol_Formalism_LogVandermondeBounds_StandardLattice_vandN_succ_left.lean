-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.vandN_succ_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:51.987824+00:00
-- url     : https://prove2.me/submissions/f87bb446-81aa-49c8-9b55-b09f5c6eeb5b

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
    vandN x (N + 1) = (∏ j ∈ Ico 1 (N + 1), (x 0 - x j)) * vandN (fun i => x (i + 1)) N := by
  unfold vandN
  rw [prod_range_succ', mul_comm, zero_add]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [← prod_Ico_add' (fun j => x (i + 1) - x j) (i + 1) N 1]
end Formalism.LogVandermondeBounds.StandardLattice
