-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.br_sg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:59.055293+00:00
-- url     : https://prove2.me/submissions/180e1f5a-2692-44e0-9944-f26fa4617e8e

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r_sg

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
theorem _root_.solution : P.b * P.x⁻¹ ≤ sg P K * P.b := by
  have := mul_le_mul_of_nonneg_left F.r_sg F.b0
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
