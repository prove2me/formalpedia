-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.norm_nat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:35.731334+00:00
-- url     : https://prove2.me/submissions/5df3290f-495b-4cfc-8f51-b5a2d6b14f83

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
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (t : ℕ) (ht : t ≠ 0) : ‖(t : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p t : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast ht), Padic.valuation_natCast]
end Formalism.GM.gammaIntegralityLemmas
