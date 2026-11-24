-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.leadj_applyWord_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:21.073979+00:00
-- url     : https://prove2.me/submissions/01990719-44a4-4aa2-9a55-0713b9ecc779

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (l1 ++ l2) F = applyWord ℚ l1 (applyWord ℚ l2 F) := by
  unfold applyWord
  rw [List.foldr_append]
end Formalism.GradedWeylDivisibility
