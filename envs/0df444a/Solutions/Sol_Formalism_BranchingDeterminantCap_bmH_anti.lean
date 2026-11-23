-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmH_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:27:45.574665+00:00
-- url     : https://prove2.me/submissions/6f19f444-363a-45ad-8593-5067f4bea693

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

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
theorem _root_.solution {n : ℕ} (L : Fin (n + 1) → ℤ) (μ : Fin n → ℤ) (h : Interlace L μ) : Antitone L := by
  exact Fin.antitone_iff_succ_le.mpr fun i => le_trans (h i).2 (h i).1
end Formalism.BranchingDeterminantCap
