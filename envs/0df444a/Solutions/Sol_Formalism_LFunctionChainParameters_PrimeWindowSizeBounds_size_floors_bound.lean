-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_floors_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:53.219394+00:00
-- url     : https://prove2.me/submissions/cf8f1e33-fbb3-4472-91ab-ebca9f7f5759

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale1__403e671ab8fd
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Epos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_la0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_lax
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sg0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_monoG
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyX__ac9c7cc18615

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
theorem _root_.solution : SizeFloors := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tFloors unitU
  apply scale1' hm hT (mul_nonneg F.sg0 F.b0)
  rw [F.hXpp, F.loga]
  unfold Par.f
  have h1 := F.C0; have h2 := F.CK; have h3 := F.npos; have h4 := F.nE; have h5 := F.N0
  have h6 := F.NE; have h7 := F.la0; have h8 := F.lax; have h9 := F.xpos; have h10 := F.Xpos
  have h11 := F.Kpos; have h12 := F.Epos
  calc 2 * P.C * (2 * P.n) * (P.x * P.n * X) * (P.N ^ 2 * (P.lx + z) + 2 * (P.lx + z) ^ 2)
      ≤ 2 * K * (2 * E) * (P.x * E * X) * (E ^ 2 * P.x + 2 * P.x ^ 2) := by gcongr
    _ = 4 * K * (E ^ 4 * P.x ^ 2) * X + 8 * K * (E ^ 2 * P.x ^ 3) * X := by ring
    _ ≤ 4 * K * (E ^ 4 * P.x ^ 3) * X + 8 * K * (E ^ 4 * P.x ^ 3) * X := by
        have a1 := F.monoG (i := 4) (j := 2) (i' := 4) (j' := 3) (by norm_num) (by norm_num)
        have a2 := F.monoG (i := 2) (j := 3) (i' := 4) (j' := 3) (by norm_num) (by norm_num)
        gcongr
    _ = 12 * K * (E ^ 4 * P.x ^ 3) * X := by ring
    _ ≤ sg P K * P.b := F.polyX' (le_refl _) (le_refl _) (by norm_num) (by norm_num)
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
