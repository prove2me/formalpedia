-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_emb_minor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:55.275283+00:00
-- url     : https://prove2.me/submissions/62cdb342-d165-42a6-9016-f9c5e6bf78d9

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_X
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (c : Fin s → Fin n) :
    emb R n (Matrix.of fun p q : Fin s => (X (I p, c q) : MvPolynomial (Fin n × Fin n) R)).det =
      (Matrix.of fun p q : Fin s => (X ((I p).castSucc, c q) : BP R n)).det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [bmF_emb_X]
end Formalism.BranchingDeterminantCap
