-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.etaPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:30.502662+00:00
-- url     : https://prove2.me/submissions/3546091d-ff45-4e86-b0a0-17758586f0e8

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
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) (c : Fin r) :
    etaPart m c = m (Fin.last N, c) := by
  rfl
end Formalism.GM.FrozenVariableComponents
