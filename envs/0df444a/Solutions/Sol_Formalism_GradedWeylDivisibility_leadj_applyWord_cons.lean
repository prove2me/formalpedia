-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.leadj_applyWord_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:21.372752+00:00
-- url     : https://prove2.me/submissions/d5750ca1-14f0-43d4-bc6c-77176db399d8

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
theorem _root_.solution {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := by
  rfl
end Formalism.GradedWeylDivisibility
