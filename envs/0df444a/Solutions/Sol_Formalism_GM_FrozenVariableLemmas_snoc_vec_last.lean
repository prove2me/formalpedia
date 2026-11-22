-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.snoc_vec_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:56.665204+00:00
-- url     : https://prove2.me/submissions/b6fda3ab-056b-4204-81f1-ce1c026d2b20

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution {N : ℕ} (LL : M.Letters N) (n : ℕ) :
    (LL.snoc n).vec (Fin.last N) = false := by
  simp [M.Letters.snoc]
end Formalism.GM.FrozenVariableLemmas
