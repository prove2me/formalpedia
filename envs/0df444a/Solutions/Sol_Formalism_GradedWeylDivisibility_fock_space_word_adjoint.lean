-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fock_space_word_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:18.98884+00:00
-- url     : https://prove2.me/submissions/00fa3de5-78d2-4a3a-b91b-126240d39e6a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_applyWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_applyWord_append
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_transposeWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQRowDivAdj
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
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; simp [applyWord, transposeWord]
  | cons x w ih =>
    intro F G
    rw [leadj_applyWord_cons, fockQRowDivAdj, ih, leadj_transposeWord_cons, leadj_applyWord_append]
    simp [applyWord]
end Formalism.GradedWeylDivisibility
