-- Prove2me | solution 1 for Formalism.G0.MarkedRunP.mem_cell_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:56.616326+00:00
-- url     : https://prove2.me/submissions/45fde5d6-421b-40e2-873e-d36aaf68bd29

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_MarkedRun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.MarkedRunP
namespace Formalism.G0.MarkedRunP
theorem _root_.solution (r u s q x : ℕ) :
    x ∈ cell r u s (q + 1) ↔
      s * ((6 * r + 1) * u) + q * u ≤ x ∧ x < s * ((6 * r + 1) * u) + q * u + u := by
  simp only [cell, Finset.mem_Ico, Nat.add_sub_cancel, add_mul, one_mul, add_assoc]
end Formalism.G0.MarkedRunP
