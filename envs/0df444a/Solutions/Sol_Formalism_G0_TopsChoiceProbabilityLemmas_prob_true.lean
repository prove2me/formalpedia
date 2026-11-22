-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:24.420264+00:00
-- url     : https://prove2.me/submissions/1c7cc99e-8e29-4491-9c17-c0d0798cd125

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

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
theorem _root_.solution (S : Finset ℕ) (δ : ℝ) : P S δ (fun _ => True) = 1 := by
  unfold P
  simp only [if_true]
  rw [sum_pow_mul_eq_add_pow]
  simp
end Formalism.G0.TopsChoiceProbabilityLemmas
