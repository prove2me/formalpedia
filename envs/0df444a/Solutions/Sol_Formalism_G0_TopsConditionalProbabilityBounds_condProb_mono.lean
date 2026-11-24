-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityBounds.condProb_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:42.490604+00:00
-- url     : https://prove2.me/submissions/e2f4bd5a-faf7-4981-b2fe-e584295ca1c0

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartC
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_weight_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityBounds
open Finset
namespace Formalism.G0.TopsConditionalProbabilityBounds
theorem _root_.solution (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (A B : Finset ℕ → Prop)
    (h : ∀ T, 0 ∈ T → A T → B T) : condProb n δ A ≤ condProb n δ B := by
  classical
  unfold condProb
  apply sum_le_sum
  intro T _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h T h1.1 h1.2⟩ h2
  · exact weight_nonneg n δ hδ0 hδ1 T
  · exact le_rfl
end Formalism.G0.TopsConditionalProbabilityBounds
