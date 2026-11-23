-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_fil_add_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:45.624742+00:00
-- url     : https://prove2.me/submissions/56250f98-033a-4424-9392-8328120376d1

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {F L : BP R n} (hF : bmF_Fil D F)
    (hL : IsLow D L) : bmF_Fil D (F + L) := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h1 | h1
  · exact hF m h1
  · exact le_of_lt (hL m h1)
end Formalism.BranchingDeterminantCap
