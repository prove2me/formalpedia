-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_zmon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.953724+00:00
-- url     : https://prove2.me/submissions/ca0346df-33b5-4161-bbbd-ddc21dbf7c6e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_X_last
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
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) :
    rowAct R (extM R g) (zmon R n b) = zmon R n b := by
  simp only [zmon, map_prod, map_pow, bmF_rowAct_X_last]
end Formalism.BranchingDeterminantCap
