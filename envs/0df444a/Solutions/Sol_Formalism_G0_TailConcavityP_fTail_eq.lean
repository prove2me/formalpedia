-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.fTail_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:45.22886+00:00
-- url     : https://prove2.me/submissions/a02148b9-a3a9-41e2-bcde-e546b13cd523

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
import Theorems.Thm_Formalism_G0_TailConcavityP_choose_cast

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
open Formalism.G0.TailConcavityP
namespace Formalism.G0.TailConcavityP
theorem _root_.solution (k y : ℕ) :
    fTail k y = ∑ i ∈ range k, (Real.log ((y : ℝ) + i + 1) - Real.log ((i : ℝ) + 1)) := by
  unfold fTail
  rw [choose_cast, Real.log_prod]
  · apply sum_congr rfl
    intro i _
    rw [Real.log_div] <;> positivity
  · intro i _
    positivity
end Formalism.G0.TailConcavityP
