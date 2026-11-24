-- Prove2me | solution 1 for Formalism.LatticeIndexTer.phm_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:53.259387+00:00
-- url     : https://prove2.me/submissions/398a1ebd-936a-4651-9295-ef0b0a5fd0cb

import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Theorems.Thm_Formalism_LatticeIndexTer_ph_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Finset
namespace Formalism.LatticeIndexTer
theorem _root_.solution : Monotone phm := by
  intro x y hxy
  unfold phm
  exact ph_mono (le_max_right _ _) (max_le (le_trans hxy (le_max_left _ _)) (le_max_right _ _))
end Formalism.LatticeIndexTer
