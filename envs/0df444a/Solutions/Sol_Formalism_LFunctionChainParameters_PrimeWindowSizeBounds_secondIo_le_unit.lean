-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.secondIo_le_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:53.80952+00:00
-- url     : https://prove2.me/submissions/18cfb8a9-a932-4e10-b8cc-5e0919263ec3

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_size_second_io_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_sigma_le_one
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_unitU_nonneg

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
theorem _root_.solution {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (hm : 0 ≤ m) (hT : 1 ≤ T) : tSecondIo P m T ≤ unitU P m T := by
  have h := size_second_io_bound P e K m T hW hL hm hT
  have h1 := (sigma_le_one P e K hW hL).2
  have := mul_le_mul_of_nonneg_right h1 (unitU_nonneg (P := P) hm hT)
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
