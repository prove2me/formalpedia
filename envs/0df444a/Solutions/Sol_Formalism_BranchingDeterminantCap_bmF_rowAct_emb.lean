-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:54.156705+00:00
-- url     : https://prove2.me/submissions/5d94ec04-5ea5-440d-9d4b-2cb422123c7a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_rowAction_X_sum
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_X
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_X_castSucc
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
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    rowAct R (extM R g) (emb R n f) = emb R n (rowAct R g f) := by
  have : (rowAct R (extM R g)).comp (emb R n) = (emb R n).comp (rowAct R g) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, bmF_emb_X, bmF_rowAct_X_castSucc, rowAction_X_sum]
    simp [emb, rename_C]
  exact AlgHom.congr_fun this f
end Formalism.BranchingDeterminantCap
