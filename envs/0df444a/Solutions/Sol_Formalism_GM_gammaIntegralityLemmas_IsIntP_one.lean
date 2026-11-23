-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IsIntP.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:26.610056+00:00
-- url     : https://prove2.me/submissions/0c91521a-3a55-4785-8ef0-de937ff1ae77

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
theorem _root_.solution : IsIntP (1 : MvPolynomial σ ℚ_[p]) := by
  rw [← C_1]; exact IsIntP.C (by simp)
end IsIntP
end Formalism.GM.gammaIntegralityLemmas
