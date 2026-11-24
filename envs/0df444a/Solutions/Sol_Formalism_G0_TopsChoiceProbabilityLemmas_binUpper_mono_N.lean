-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.binUpper_mono_N
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:34.775495+00:00
-- url     : https://prove2.me/submissions/c835ddce-00e1-40a8-90f6-c878b2df1c11

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
theorem _root_.solution (G : ℕ) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) :
    binUpper G δ N ≤ binUpper G δ (N - 1) := by
  unfold binUpper
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (Nat.sub_le N 1) le_rfl)
  intro j _ _
  have : 0 ≤ 1 - δ := by linarith
  positivity
end Formalism.G0.TopsChoiceProbabilityLemmas
