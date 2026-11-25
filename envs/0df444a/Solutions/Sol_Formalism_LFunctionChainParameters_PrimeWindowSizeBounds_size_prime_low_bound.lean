-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_prime_low_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:54.256579+00:00
-- url     : https://prove2.me/submissions/26d61481-7147-4bbc-a033-6383e3df0f50

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
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Epos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hundred_z_le_x
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyv__5d511584b185

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
theorem _root_.solution : SizePrLow := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tPrLow unitU
  have key : 2 * Real.log 4 * (P.p₀ * P.Q₁) ≤ sg P K * P.b := by
    unfold Par.Q₁
    rw [F.hbp]
    have h1 := F.C0; have h2 := F.CK; have h3 := F.r0; have h4 := F.rE; have h5 := F.pE
    have h6 := F.lx0; have h7 : P.lx ≤ P.x := by linarith [F.lxz, F.hundred_z_le_x, F.zpos]
    have h8 := F.v0; have h9 := F.xpos; have h11 := F.Kpos; have h12 := F.Epos
    have h13 := log_four_le_three_halves; have h14 := log_four_nonneg
    have h15 : (0 : ℝ) ≤ P.p₀ := Nat.cast_nonneg _
    calc 2 * Real.log 4 * (P.p₀ * (P.C * P.rG * (P.x * v) * P.lx))
        ≤ 2 * (3 / 2) * (E * (K * E * (P.x * v) * P.x)) := by gcongr
      _ = 3 * K * (E ^ 2 * P.x ^ 2) * v := by ring
      _ ≤ sg P K * P.b := F.polyv' (by norm_num) (by norm_num) (by norm_num)
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
