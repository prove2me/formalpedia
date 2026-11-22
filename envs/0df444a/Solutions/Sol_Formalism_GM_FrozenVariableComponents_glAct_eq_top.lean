-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.glAct_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:12.36375+00:00
-- url     : https://prove2.me/submissions/a1c93777-2f8d-47ad-8cc7-1df442cfea0c

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL j c d = ∑ i : Fin N, if (i : ℕ) < j then top p LL i c d else 0 := rfl
end Formalism.GM.FrozenVariableComponents
