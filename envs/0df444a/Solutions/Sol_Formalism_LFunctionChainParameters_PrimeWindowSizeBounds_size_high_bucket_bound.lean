-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_high_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:03.880136+00:00
-- url     : https://prove2.me/submissions/27103595-c071-4c7b-b060-eb5447bbfcf1

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_two_le_one_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_X1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_n1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_apos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_log_le_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_v_le_b
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
theorem _root_.solution : SizeHigh := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tHigh unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hXpp1 : 1 ≤ P.x * P.n * X :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le F.x1 F.n1) F.X1
  have c3 : Real.log (2 * P.Xpp) ≤ 4 * z := by
    rw [F.hXpp, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (mul_pos h9 F.npos).ne' F.Xpos.ne', Real.log_mul h9.ne' F.npos.ne', F.logX]
    have a1 : Real.log P.n ≤ z := F.log_le_alt F.npos F.nE
    have a2 : Real.log P.x ≤ z := F.lxz
    linarith [log_two_le_one_alt, F.uz, F.z1]
  have c30 : 0 ≤ Real.log (2 * P.Xpp) := by
    rw [F.hXpp]; exact Real.log_nonneg (by linarith)
  have ht0 := F.th0; have ht := F.thx
  have c4 : P.a * P.th ^ 2 ≤ P.b * P.x⁻¹ := by
    rw [F.ha]
    calc P.x * P.b * P.th ^ 2 ≤ P.x * P.b * P.x⁻¹ ^ 2 := by gcongr
      _ = P.b * P.x⁻¹ * (P.x * P.x⁻¹) := by ring
      _ = P.b * P.x⁻¹ := by rw [F.xr, mul_one]
  have c5 : P.wpp * P.th ≤ P.b * P.x⁻¹ := by
    rw [F.hwpp]
    have a1 : v / P.n ≤ P.b := (div_le_self F.v0 F.n1).trans F.v_le_b
    have a0 : 0 ≤ v / P.n := div_nonneg F.v0 F.npos.le
    gcongr
  have c6 : 0 ≤ P.a * P.th ^ 2 + P.wpp * P.th := by
    have := F.apos
    have : 0 ≤ P.wpp := by rw [F.hwpp]; exact div_nonneg F.v0 F.npos.le
    positivity
  have key : 2 * Real.log (2 * P.Xpp) * (P.a * P.th ^ 2 + P.wpp * P.th) ≤ sg P K * P.b := by
    calc 2 * Real.log (2 * P.Xpp) * (P.a * P.th ^ 2 + P.wpp * P.th)
        ≤ 2 * (4 * z) * (P.b * P.x⁻¹ + P.b * P.x⁻¹) := by gcongr
      _ = P.b * (16 / 100) * (100 * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := F.close_sg (by norm_num) (by norm_num) (F.zr0 1) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
