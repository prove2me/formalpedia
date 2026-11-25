-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.Dop_commute_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:46.938867+00:00
-- url     : https://prove2.me/submissions/27322673-5890-43c8-b385-4b3fbb3dc5be

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_commute

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
theorem _root_.solution {ι : Type} (s : Finset ι) (u v : σ) (f g : ι → σ) :
    Commute (Dop (p := p) u v) (∑ i ∈ s, Dop (f i) (g i)) :=
  Commute.sum_right _ _ _ (fun i _ => Dop_commute _ _ _ _)
end Formalism.GM.gammaIntegralityLemmas
