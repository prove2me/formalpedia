-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_or_le_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:59.838467+00:00
-- url     : https://prove2.me/submissions/03a45a77-83d8-4d93-b591-b5d30340b33e

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_w_nonneg


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
theorem _root_.solution {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A B : Finset ℕ → Prop) :
    P U δ (fun t => A t ∨ B t) ≤ P U δ A + P U δ B := by
  classical
  unfold P
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro t _
  have := w_nonneg h0 h1 t.card (U.card - t.card)
  by_cases hA : A t <;> by_cases hB : B t <;> simp [hA, hB] <;> linarith
end Formalism.G0.TopsChoiceProbabilityLemmas
