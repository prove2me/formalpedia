-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmC_ndEv_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:31.428865+00:00
-- url     : https://prove2.me/submissions/6f681dd9-42fe-48ef-be08-eb42291441c3

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (q : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (rename some q) = q := by
  have : (ndEv R r n).comp (rename some) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun v => ?_
    simp [ndEv]
  exact AlgHom.congr_fun this q
end Formalism.BranchingDeterminantCap
