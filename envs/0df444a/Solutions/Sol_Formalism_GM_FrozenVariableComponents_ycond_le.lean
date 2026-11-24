-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.ycond_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:42.514014+00:00
-- url     : https://prove2.me/submissions/521a070c-5169-4ee2-a353-73b3de0fc93e

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
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    YCond p (r := r) LL j M ≤ MvPolynomial.restrictSupport ℚ_[p]
        {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} := by
  unfold Formalism.GM.M.YCond
  exact sSup_le (fun T hT => hT.1)
end Formalism.GM.FrozenVariableComponents
