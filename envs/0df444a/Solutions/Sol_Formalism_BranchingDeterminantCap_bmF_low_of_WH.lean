-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_low_of_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:46.343581+00:00
-- url     : https://prove2.me/submissions/48998689-4bb4-44b0-8143-8709142bd385

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {F : BP R n} {β : Fin n → ℤ}
    (hF : IsWeightedHomogeneous (zW n) F β) (hβ : omg β < D) : IsLow D F := by
  intro m hm
  rw [hF (mem_support_iff.mp hm)]
  exact hβ
end Formalism.BranchingDeterminantCap
