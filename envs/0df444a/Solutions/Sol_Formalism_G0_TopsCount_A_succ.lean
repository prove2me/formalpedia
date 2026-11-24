-- Prove2me | solution 1 for Formalism.G0.TopsCount.A_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:42.593046+00:00
-- url     : https://prove2.me/submissions/0dd33534-4ef6-45a9-a77e-0d5904b92e5e

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsCount
namespace Formalism.G0.TopsCount
theorem _root_.solution (m : ℕ) (δ : ℝ) (K : ℕ) : A m δ (K + 1) = A m δ K + a m δ K := by
  unfold A; rw [sum_range_succ]
end Formalism.G0.TopsCount
