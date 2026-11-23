-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.sb_le_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:47.443726+00:00
-- url     : https://prove2.me/submissions/8889663a-7f0d-4254-8efc-dc158f51d4d4

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sb1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
theorem _root_.solution : sb ≤ P.b := by
  rw [F.hb]
  have := F.sb1
  exact le_mul_of_one_le_left (by linarith) this
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
