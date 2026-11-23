-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:26.585827+00:00
-- url     : https://prove2.me/submissions/e89036b4-fe21-455b-97ec-37991223c317

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
namespace IsIntP
theorem _root_.solution {P : MvPolynomial σ ℚ_[p]} (h : IsIntP P) : IsIntP (-P) := by
  intro β; rw [coeff_neg, norm_neg]; exact h β
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
