-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.close_sg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:58.900023+00:00
-- url     : https://prove2.me/submissions/ae4e77da-bbf6-4ee3-bc49-08f3cea5666a

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0

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
theorem _root_.solution {c w : ℝ} (_hc0 : 0 ≤ c) (hc : c ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ sg P K) :
    P.b * c * w ≤ sg P K * P.b := by
  have h1 : c * w ≤ 1 * sg P K := mul_le_mul hc hw hw0 zero_le_one
  have h2 := mul_le_mul_of_nonneg_left h1 F.b0
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
