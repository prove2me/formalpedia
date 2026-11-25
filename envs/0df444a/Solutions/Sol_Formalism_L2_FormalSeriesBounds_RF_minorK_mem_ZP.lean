-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.minorK_mem_ZP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:54.325041+00:00
-- url     : https://prove2.me/submissions/fe4db8ab-0ccb-4e34-898d-69bd62fe083d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_X_mem_ZP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_det_mem

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (N N' k : ℕ) : minorK C N N' k ∈ ZP C (Fin N × Fin N') := by
  unfold minorK
  split_ifs with h
  · exact det_mem _ _ fun i j => X_mem_ZP _
  · exact one_mem _
end Formalism.L2.FormalSeriesBounds.RF
