-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.g_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:11.140883+00:00
-- url     : https://prove2.me/submissions/1ee5dbbb-b6f8-42fd-a8dd-48b8aa8cc933

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
theorem _root_.solution (k : ℕ) {b b' : ℝ} (hb : 0 ≤ b) (h : b ≤ b') : g k b' ≤ g k b := by
  unfold g
  apply sum_le_sum
  intro i _
  apply one_div_le_one_div_of_le (by positivity) (by linarith)
end Formalism.G0.TailConcavityP
