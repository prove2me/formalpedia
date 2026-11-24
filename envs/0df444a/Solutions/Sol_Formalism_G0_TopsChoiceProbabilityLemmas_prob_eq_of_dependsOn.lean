-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_eq_of_dependsOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:33.463177+00:00
-- url     : https://prove2.me/submissions/0bd552bb-a8a2-4a22-bdf8-3ef4da3322d0

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_marginal

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
theorem _root_.solution {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) {A : Finset ℕ → Prop} (hA : Dep S A) :
    P U δ A = P S δ A := by
  rw [← prob_marginal δ hS A]
  congr 1
  funext t
  exact propext (hA t)
end Formalism.G0.TopsChoiceProbabilityLemmas
