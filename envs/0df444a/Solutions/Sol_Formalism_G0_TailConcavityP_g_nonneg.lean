-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.g_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:32.695913+00:00
-- url     : https://prove2.me/submissions/a94b96ec-98ef-4de3-88c1-4b475b56f7d8

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity

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
theorem _root_.solution (k : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ g k b := by
  unfold g
  apply sum_nonneg
  intro i _
  positivity
end Formalism.G0.TailConcavityP
