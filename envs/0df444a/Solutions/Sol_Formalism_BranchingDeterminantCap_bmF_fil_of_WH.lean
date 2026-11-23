-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_fil_of_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:45.878545+00:00
-- url     : https://prove2.me/submissions/6112e468-ddc5-435d-aa28-1d895144d675

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {F : BP R n} {β : Fin n → ℤ}
    (hF : IsWeightedHomogeneous (zW n) F β) : bmF_Fil (omg β) F := by
  intro m hm
  exact le_of_eq (congrArg omg (hF (mem_support_iff.mp hm)))
end Formalism.BranchingDeterminantCap
