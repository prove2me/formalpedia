-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_not_eq_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:20.503459+00:00
-- url     : https://prove2.me/submissions/1f7ab90e-7dcb-4a23-80bd-8b624294cf85

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_true

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) :
    P U δ (fun t => ¬ A t) = 1 - P U δ A := by
  classical
  rw [← prob_true U δ, eq_sub_iff_add_eq]
  unfold P
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases h : A t <;> simp [h]
end Formalism.G0.TopsChoiceProbabilityLemmas
