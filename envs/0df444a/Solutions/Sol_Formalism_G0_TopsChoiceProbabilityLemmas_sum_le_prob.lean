-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.sum_le_prob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:20.35027+00:00
-- url     : https://prove2.me/submissions/8c860eb9-1876-469e-a7b2-52c4016e597f

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
theorem _root_.solution {S : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ → Prop}
    (Fam : Finset (Finset ℕ)) (hF : ∀ t ∈ Fam, t ⊆ S ∧ A t) :
    ∑ t ∈ Fam, δ ^ t.card * (1 - δ) ^ (S.card - t.card) ≤ P S δ A := by
  classical
  unfold P
  refine le_trans (le_of_eq (sum_congr rfl fun t ht => ?_))
    (sum_le_sum_of_subset_of_nonneg (fun t ht => mem_powerset.2 (hF t ht).1) ?_)
  · rw [if_pos (hF t ht).2]
  · intro t _ _
    split_ifs
    · exact w_nonneg h0 h1 _ _
    · exact le_rfl
end Formalism.G0.TopsChoiceProbabilityLemmas
