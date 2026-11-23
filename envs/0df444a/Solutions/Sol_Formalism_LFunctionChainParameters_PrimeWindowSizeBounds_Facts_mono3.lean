-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.mono3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:14.691056+00:00
-- url     : https://prove2.me/submissions/dca5a8b2-b094-46c7-acb0-8c894e29a14e

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_monoG

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
theorem _root_.solution {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) : E ^ i * P.x ^ j ≤ E ^ 4 * P.x ^ 4 * P.x⁻¹ := by
  have h : E ^ 4 * P.x ^ 4 * P.x⁻¹ = E ^ 4 * P.x ^ 3 := by
    rw [show P.x ^ 4 = P.x ^ 3 * P.x by ring, mul_assoc, mul_assoc, F.xr, mul_one]
  rw [h]
  exact F.monoG hi hj
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
