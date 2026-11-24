-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.xprime_q_two_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:12.064833+00:00
-- url     : https://prove2.me/submissions/d396d558-c2e3-4bbc-87e9-6131e0612f33

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos

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
theorem _root_.solution {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8) :
    P.Xp * P.Q₂ = P.C * P.b + P.C * X * (P.η + P.Sc) + P.C * (P.b / P.n) * P.lx * w8
      + P.C * X * P.t * P.lx * w8 + X * P.bo := by
  unfold Par.Q₂
  rw [F.hXp, F.hbp, F.hwpp, F.hδ, ← F.hvX, div_inv_eq_mul]
  have h1 := F.xpos.ne'
  have h2 := F.npos.ne'
  field_simp
  ring
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
