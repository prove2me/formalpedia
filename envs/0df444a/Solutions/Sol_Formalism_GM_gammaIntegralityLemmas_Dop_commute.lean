-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.Dop_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:58.594862+00:00
-- url     : https://prove2.me/submissions/25ddb0c7-7629-497f-905c-76995a109b2c

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_pderiv_comm__40dd41c8beb1
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_apply

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
variable {σ : Type} [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (u v u' v' : σ) : Commute (Dop (p := p) u v) (Dop u' v') := by
  apply LinearMap.ext; intro q
  simp only [Module.End.mul_apply, Dop_apply]
  rw [pderiv_comm' v u', pderiv_comm' u u', pderiv_comm' v v', pderiv_comm' u v']
end Formalism.GM.gammaIntegralityLemmas
