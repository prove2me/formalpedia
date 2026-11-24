-- Prove2me | solution 1 for Formalism.REAL.rho_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:02.272215+00:00
-- url     : https://prove2.me/submissions/64f35756-330f-46cb-b297-1cd1749c3f39

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard

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
theorem _root_.solution {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) ≤ n := by
  have h : (univ.filter p).card ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast h
end Formalism.REAL
