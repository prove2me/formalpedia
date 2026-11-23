-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.FT_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:12.736284+00:00
-- url     : https://prove2.me/submissions/37f29dfd-3ba8-42d8-bce7-a2eaf3806122

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

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
theorem _root_.solution (c : Fin r) (T : Finset (Fin r)) (hc : c ∉ T) :
    FT (p := p) w e (insert c T) = Dop (w c) (e c) + FT w e T := by
  unfold FT; rw [sum_insert hc]
end Formalism.GM.gammaIntegralityLemmas
