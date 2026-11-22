-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.scale2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:01:29.417867+00:00
-- url     : https://prove2.me/submissions/963b5edc-994f-419c-95d0-ddb83de72446

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers

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
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution {m T q c b : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) (h : q ≤ c * b) :
    m * T * q ≤ c * (T * m * b) := by
  have h1 : (m * T) * q ≤ (m * T) * (c * b) :=
    mul_le_mul_of_nonneg_left h (mul_nonneg hm (by linarith))
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
