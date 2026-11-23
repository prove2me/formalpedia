-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:58.061314+00:00
-- url     : https://prove2.me/submissions/fbcbdfba-d3c2-4621-9217-8c5bdfcfc142

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_neg
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_neg

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
theorem _root_.solution {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P - P') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
