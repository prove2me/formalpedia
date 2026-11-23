-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.FT_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:05.561451+00:00
-- url     : https://prove2.me/submissions/d932a201-4fdc-4677-a68e-f0725d3c2f19

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
theorem _root_.solution (T : Finset (Fin r)) (H : MvPolynomial σ ℚ_[p]) :
    FT (p := p) w e T H = ∑ c ∈ T, Dop (w c) (e c) H := by
  unfold FT; exact LinearMap.sum_apply _ _ _
end Formalism.GM.gammaIntegralityLemmas
