-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_low_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:53.672802+00:00
-- url     : https://prove2.me/submissions/83eb1909-03bf-4ea1-ae04-de985d5f4ab2

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {L L' : BP R n} (h : IsLow D L)
    (h' : IsLow D L') : IsLow D (L + L') := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h1 | h1
  · exact h m h1
  · exact h' m h1
end Formalism.BranchingDeterminantCap
