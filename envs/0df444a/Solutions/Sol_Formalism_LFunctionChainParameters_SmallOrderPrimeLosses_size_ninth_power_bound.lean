-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.size_ninth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:00.229868+00:00
-- url     : https://prove2.me/submissions/27f34473-71fe-498f-b70b-20d205ebc125

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_close_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution {P : Par} {e K : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) :
    2 * P.a * (P.x ^ 9)⁻¹ ≤ sg P K * P.b := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hr0 := F.rpos
  have hr1 : P.x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ F.x1
  have h7 : P.x⁻¹ ^ 7 ≤ 1 := pow_le_one₀ hr0.le hr1
  have h70 : 0 ≤ P.x⁻¹ ^ 7 := pow_nonneg hr0.le 7
  rw [F.ha, ← inv_pow]
  calc 2 * (P.x * P.b) * P.x⁻¹ ^ 9
      = P.b * (2 / 100 * (P.x * P.x⁻¹) * P.x⁻¹ ^ 7) * (100 * z ^ 0 * P.x⁻¹) := by ring
    _ ≤ sg P K * P.b := by
        rw [F.xr]
        exact F.close_sg (by linarith) (by linarith) (F.zr0 0) (F.zr_sg (by norm_num))
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
