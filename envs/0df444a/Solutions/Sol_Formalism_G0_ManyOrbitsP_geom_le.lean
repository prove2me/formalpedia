-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.geom_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:56.505222+00:00
-- url     : https://prove2.me/submissions/cb9d4864-16c4-4965-9fc3-3c8d66a00ef1

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits

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
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, s ^ i ≤ 2 - 2 * s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hsn : 0 ≤ s ^ n := pow_nonneg hs0 n
    nlinarith [mul_le_mul_of_nonneg_left hs hsn]
end Formalism.G0.ManyOrbitsP
