-- Prove2me | solution 1 for Formalism.REAL.parabolic_character_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:06.076176+00:00
-- url     : https://prove2.me/submissions/58d2be5c-bab2-4c0a-88cb-b44e35923715

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_anti_iff
import Theorems.Thm_Formalism_REAL_mem_cartanP_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : PChar := by
  intro n ε X
  exact ⟨mem_cartanP_iff ε X, fun h => (f1alg_anti_iff ε X).mp h.2⟩
end Formalism.REAL
