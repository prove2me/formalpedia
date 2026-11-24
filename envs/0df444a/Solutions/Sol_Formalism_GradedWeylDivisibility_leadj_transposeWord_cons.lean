-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.leadj_transposeWord_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:21.959844+00:00
-- url     : https://prove2.me/submissions/6672db91-2219-417e-a6d2-e1567ecdea53

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
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
theorem _root_.solution {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]
end Formalism.GradedWeylDivisibility
