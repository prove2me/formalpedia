-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.Dop_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:26.045507+00:00
-- url     : https://prove2.me/submissions/56077d93-8a38-43c4-97bc-88a9c28ea175

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
variable {σ : Type} [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (u v : σ) (q : MvPolynomial σ ℚ_[p]) : Dop u v q = pderiv u (pderiv v q) := rfl
end Formalism.GM.gammaIntegralityLemmas
