-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fischerInnerRowActionAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:53.003434+00:00
-- url     : https://prove2.me/submissions/c0340191-ca8d-4adf-a99e-8f901de39e66

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_rowAct_eq_sub
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_rowMat_conjTranspose
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_subAdj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockRowAdj := by
  intro r n g f h
  rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]
end Formalism.GradedWeylDivisibility
