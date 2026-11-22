-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.llPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:30.498649+00:00
-- url     : https://prove2.me/submissions/58b483cb-296e-4e56-96a5-d4ebfbeee997

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
open MvPolynomial Finset
variable {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) (x : Fin N × Fin r) :
    llPart m x = m (Fin.castSucc x.1, x.2) := by
  rfl
end Formalism.GM.FrozenVariableComponents
