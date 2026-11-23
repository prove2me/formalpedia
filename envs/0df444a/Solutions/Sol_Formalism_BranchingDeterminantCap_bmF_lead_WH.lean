-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_lead_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:17.836794+00:00
-- url     : https://prove2.me/submissions/481ed4eb-d5c9-446e-9873-9ffe92c89bd4

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zmon_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zW_castSucc
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    IsWeightedHomogeneous (zW n) (zmon R n b * emb R n f) (fun s => (b s : ℤ)) := by
  simpa using (bmF_zmon_WH R n b).mul (bmF_emb_WH (zW n) (fun a s => bmF_zW_castSucc a s) f)
end Formalism.BranchingDeterminantCap
