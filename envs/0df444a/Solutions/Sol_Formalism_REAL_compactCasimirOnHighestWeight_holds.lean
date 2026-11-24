-- Prove2me | solution 1 for Formalism.REAL.compactCasimirOnHighestWeight_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:30.346845+00:00
-- url     : https://prove2.me/submissions/1c693e76-8d90-4a86-9b1e-495497c67076

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
import Theorems.Thm_Formalism_REAL_casKHW_term
import Theorems.Thm_Formalism_REAL_casKHW_arith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : CasKHighest := by
  intro V _ _ n ε E μ w hG hK
  unfold CasK
  simp only [LinearMap.sum_apply]
  simp_rw [casKHW_term V n ε E μ w hG hK]
  rw [← casKHW_arith ε μ]
  simp_rw [← Finset.sum_smul]
  push_cast
  rfl
end Formalism.REAL
