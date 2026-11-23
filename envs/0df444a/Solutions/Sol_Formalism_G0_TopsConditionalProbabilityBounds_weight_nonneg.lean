-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityBounds.weight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:27.596153+00:00
-- url     : https://prove2.me/submissions/3df70b3f-aff1-4418-8a42-15b22ac98b78

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartC

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
theorem _root_.solution (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (T : Finset ℕ) :
    0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) :=
  mul_nonneg (pow_nonneg hδ0 _) (pow_nonneg (by linarith) _)
end Formalism.G0.TopsConditionalProbabilityBounds
