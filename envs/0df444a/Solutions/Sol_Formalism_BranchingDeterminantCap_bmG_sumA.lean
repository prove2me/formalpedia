-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_sumA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:27:45.090953+00:00
-- url     : https://prove2.me/submissions/302228f3-42d5-49e7-a59b-21c70b446382

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_single_castLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (i : Fin n) :
    (∑ p : Fin (i.val + 1), (Pi.single (rowsA i p) 1 : Fin (n + 1) → ℕ)) = initW (n + 1) (i.val + 1) :=
  sum_single_castLE (by omega : i.val + 1 ≤ n + 1)
end Formalism.BranchingDeterminantCap
