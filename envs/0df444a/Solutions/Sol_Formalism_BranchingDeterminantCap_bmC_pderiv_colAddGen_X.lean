-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmC_pderiv_colAddGen_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:31.659148+00:00
-- url     : https://prove2.me/submissions/af94f8a7-e91f-4344-94a7-f885cf0fbe48

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    (v : Fin r × Fin n) :
    pderiv none (colAddGen R l j (X v)) = colAddGen R l j (ndE R r n l j (X v)) := by
  by_cases h : v.2 = j
  · simp [colAddGen, ndE, mkDerivation_X, h, hlj, Derivation.leibniz, pderiv_X, Pi.single_apply]
  · simp [colAddGen, ndE, mkDerivation_X, h, pderiv_X, Pi.single_apply]
end Formalism.BranchingDeterminantCap
