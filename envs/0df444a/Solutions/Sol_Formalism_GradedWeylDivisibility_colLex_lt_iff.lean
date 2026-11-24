-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.colLex_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:52.683554+00:00
-- url     : https://prove2.me/submissions/e7511205-e791-4f4e-9ad8-b0673c147714

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ} :
    c ≺[colLex r n] d ↔ toLex (Finsupp.domCongr (cmIdx r n) c) < toLex (Finsupp.domCongr (cmIdx r n) d) := Iff.rfl
end Formalism.GradedWeylDivisibility
