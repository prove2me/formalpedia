-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_second_io_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:59.879797+00:00
-- url     : https://prove2.me/submissions/a1659ee1-2f12-4a80-9c10-cc236a00125c

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_le_three_halves
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_two_le_one_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr_sg
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
theorem _root_.solution : SizeSecondIo := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tSecondIo unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos; have hz1 := F.z1
  have hY0 : 0 < P.Y := by linarith [F.Y1]
  have c3 : Real.log P.Y + Real.log 4 ≤ 4 * z := by
    have a2 : Real.log P.Y ≤ Real.log (2 * X) := Real.log_le_log hY0 F.YX
    rw [Real.log_mul (by norm_num) F.Xpos.ne', F.logX] at a2
    linarith [log_two_le_one_alt, log_four_le_three_halves, F.uz]
  have c30 : 0 ≤ Real.log P.Y + Real.log 4 := add_nonneg (Real.log_nonneg F.Y1) log_four_nonneg
  have hs0 := F.s0
  have hs : P.s₀ ≤ P.x⁻¹ ^ 2 := by rw [← F.r2]; exact F.sx
  have c4 : P.s₀ / P.θ + P.s₀ ≤ P.x⁻¹ ^ 2 * (2 * z) := by
    rw [F.hθ, div_inv_eq_mul]
    have : P.s₀ * z + P.s₀ = P.s₀ * (z + 1) := by ring
    rw [this]
    gcongr
    linarith
  have c40 : 0 ≤ P.s₀ / P.θ + P.s₀ := by
    rw [F.hθ, div_inv_eq_mul]; positivity
  have key : (P.s₀ / P.θ + P.s₀) * (4 * P.a * (Real.log P.Y + Real.log 4)) ≤ sg P K * P.b := by
    rw [F.ha]
    calc (P.s₀ / P.θ + P.s₀) * (4 * (P.x * P.b) * (Real.log P.Y + Real.log 4))
        ≤ (P.x⁻¹ ^ 2 * (2 * z)) * (4 * (P.x * P.b) * (4 * z)) := by gcongr
      _ = P.b * (32 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 2 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 2) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
