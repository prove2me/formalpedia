-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:32.44509+00:00
-- url     : https://prove2.me/submissions/096c558f-7798-47ac-b414-c3023cc27b8c

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint
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
theorem _root_.solution {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) (A : Finset ℕ → Prop) :
    P U δ (fun t => A (t ∩ S)) = P S δ A := by
  have h := prob_and_eq_mul_of_disjoint S (U \ S) δ disjoint_sdiff A (fun _ => True)
  rw [prob_true, mul_one] at h
  simp only [and_true] at h
  rw [← h, union_sdiff_of_subset hS]
end Formalism.G0.TopsChoiceProbabilityLemmas
