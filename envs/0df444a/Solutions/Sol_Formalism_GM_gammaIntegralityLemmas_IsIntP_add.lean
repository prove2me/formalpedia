-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:41.9218+00:00
-- url     : https://prove2.me/submissions/0f22cd8b-7160-444f-9a18-0207694509c2

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
theorem _root_.solution {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P + P') := by
  intro β; rw [coeff_add]; exact (Padic.nonarchimedean _ _).trans (max_le (h β) (h' β))
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
