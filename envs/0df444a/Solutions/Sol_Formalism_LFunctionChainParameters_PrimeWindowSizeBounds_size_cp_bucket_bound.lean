-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_cp_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:14.087458+00:00
-- url     : https://prove2.me/submissions/25756d64-b67d-40d2-99dc-624ad3819c93

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_two_le_one_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_two_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Epos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Spos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hundred_z_le_x
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_apos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_la0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_la2z
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a

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
theorem _root_.solution : SizeCp := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tCp unitU
  have hl : Real.log (2 * P.a) = Real.log 2 + (P.lx + z) := by
    rw [Real.log_mul (by norm_num) F.apos.ne', F.loga]
  have hl0 : 0 ≤ Real.log (2 * P.a) := by rw [hl]; exact add_nonneg log_two_nonneg F.la0
  have hlx : Real.log (2 * P.a) ≤ P.x := by
    rw [hl]; linarith [log_two_le_one_alt, F.la2z, F.hundred_z_le_x, F.z1]
  have hSk0 : 0 ≤ P.Sk := by unfold Par.Sk; linarith [F.Sc0, F.η0, F.kx, pow_pos F.xpos 2]
  have hSk : P.Sk ≤ 3 * (E * S) := by
    unfold Par.Sk
    have a1 : S ≤ E * S := le_mul_of_one_le_left F.Spos.le F.E1
    have a2 : E ≤ E * S := le_mul_of_one_le_right F.Epos.le F.S1
    linarith [F.ScS, F.ηS, F.kE]
  have key : 2 * P.C * P.Sk * Real.log (2 * P.a) * P.Xpp ≤ sg P K * P.b := by
    rw [F.hXpp]
    have h1 := F.C0; have h2 := F.CK; have h3 := F.npos; have h4 := F.nE
    have h9 := F.xpos; have h10 := F.Xpos; have h11 := F.Kpos; have h12 := F.Epos; have h13 := F.Spos
    calc 2 * P.C * P.Sk * Real.log (2 * P.a) * (P.x * P.n * X)
        ≤ 2 * K * (3 * (E * S)) * P.x * (P.x * E * X) := by gcongr
      _ = 6 * K * (E ^ 2 * P.x ^ 2) * (X * S) := by ring
      _ ≤ sg P K * P.b := F.polyXS' (by norm_num) (by norm_num) (by norm_num)
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
