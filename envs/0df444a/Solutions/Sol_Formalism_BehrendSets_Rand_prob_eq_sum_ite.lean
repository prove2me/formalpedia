-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.prob_eq_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:58.469813+00:00
-- url     : https://prove2.me/submissions/25e3a81a-760f-429e-a3cf-61e857c83c3a

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Rand
theorem _root_.solution (X : Finset α) (δ : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    prob X δ P = ∑ T ∈ X.powerset, if P T then wt X δ T else 0 := by
  unfold prob
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : P T
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
end Formalism.BehrendSets.Rand
