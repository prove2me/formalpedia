-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.FT_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:20.931803+00:00
-- url     : https://prove2.me/submissions/ea03e949-36dc-4227-87ea-3ba252213764

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_commute_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (u v : σ) (T : Finset (Fin r)) : Commute (Dop (p := p) u v) (FT w e T) :=
  Dop_commute_sum _ _ _ _ _
end Formalism.GM.gammaIntegralityLemmas
