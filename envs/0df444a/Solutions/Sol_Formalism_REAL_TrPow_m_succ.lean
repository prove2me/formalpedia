-- Prove2me | solution 1 for Formalism.REAL.TrPow_m_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:49.816878+00:00
-- url     : https://prove2.me/submissions/5448394b-12cb-41d1-9a1e-1b225c2b1151

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (l : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    TrPow_m l (k + 1) a = l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b :=
  rfl
end Formalism.REAL
