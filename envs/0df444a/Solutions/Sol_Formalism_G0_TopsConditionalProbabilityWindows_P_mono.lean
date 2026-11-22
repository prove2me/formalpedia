-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.P_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:32:54.492777+00:00
-- url     : https://prove2.me/submissions/1cd05e44-ebb5-459c-a851-3618bf19c7be

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
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
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A B : Finset ℕ → Prop}
    (h : ∀ t ∈ U.powerset, A t → B t) : P U δ A ≤ P U δ B := by
  classical
  unfold P
  apply sum_le_sum
  intro t ht
  by_cases hA : A t
  · rw [if_pos hA, if_pos (h t ht hA)]
  · rw [if_neg hA]
    split_ifs
    · exact w_nonneg h0 h1 _ _
    · exact le_rfl
end Formalism.G0.TopsConditionalProbabilityWindows
