-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.geom_half_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:18.176253+00:00
-- url     : https://prove2.me/submissions/e81967e4-dff9-460e-801d-2d8b9fd332b4

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (k : ℕ) : ∑ j ∈ range k, ((1 : ℝ) / 2) ^ j ≤ 2 := by
  exact sum_geometric_two_le k
end Formalism.BranchingDeterminantCap
