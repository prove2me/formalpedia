-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcplead_cmIdx_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:53.346951+00:00
-- url     : https://prove2.me/submissions/e0726db9-0aff-4c6d-a156-43ba6f1b14a0

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (b : Fin r) (t : Fin n) :
    ((cmIdx r n (b, t) : Fin (n * r)) : ℕ) = b + r * t := by
  simp [cmIdx, finProdFinEquiv]
end Formalism.GradedWeylDivisibility
