-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.P_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:26.539982+00:00
-- url     : https://prove2.me/submissions/d3def9b5-a473-4553-9549-afbcded0ea70

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
theorem _root_.solution {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A : Finset ℕ → Prop) :
    0 ≤ P U δ A := by
  classical
  unfold P
  apply sum_nonneg
  intro t _
  split_ifs
  · exact w_nonneg h0 h1 _ _
  · exact le_rfl
end Formalism.G0.TopsChoiceProbabilityLemmas
