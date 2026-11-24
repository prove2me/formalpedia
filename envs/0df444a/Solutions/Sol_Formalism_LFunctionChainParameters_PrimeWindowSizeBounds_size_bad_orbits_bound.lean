-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_bad_orbits_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:52.068602+00:00
-- url     : https://prove2.me/submissions/bb5b06f6-b266-4e0b-bc06-26cb30de2e8c

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_le_three_halves
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_close_sg

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
theorem _root_.solution : SizeBad := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tBad unitU
  have h9 := F.xpos; have h11 := F.Kpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have c3 : Real.log P.Xp + Real.log 4 ≤ 3 * z := by
    rw [F.hXp, F.logX]; linarith [F.uz, log_four_le_three_halves, F.z1]
  have c30 : 0 ≤ Real.log P.Xp + Real.log 4 := by
    rw [F.hXp, F.logX]; linarith [F.u1, log_four_nonneg]
  have hβ0 := F.β0
  have hβ : P.β ≤ K * P.x⁻¹ ^ 2 := by rw [← F.r2]; exact F.βK
  have key : 32 * P.β * P.a * (Real.log P.Xp + Real.log 4) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 32 * P.β * (P.x * P.b) * (Real.log P.Xp + Real.log 4)
        ≤ 32 * (K * P.x⁻¹ ^ 2) * (P.x * P.b) * (3 * z) := by gcongr
      _ = P.b * (96 / 100 * (P.x * P.x⁻¹)) * (100 * K * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.Kzr0 1) (F.Kzr_sg (by norm_num))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
