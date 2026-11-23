-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.sb1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:16.822846+00:00
-- url     : https://prove2.me/submissions/9d41f6eb-1bc5-41b3-b521-79f22bbcff45

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_one_le_threshold_mul_powers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_one_le_x_mul_s

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
theorem _root_.solution : 1 ≤ sb := by
  have h1 : 1 ≤ K * (E ^ 4 * P.x ^ 4) * (X * S) := one_le_mul_of_one_le_of_one_le F.one_le_threshold_mul_powers F.one_le_x_mul_s
  have := F.hsb
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
