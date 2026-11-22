-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.snoc_vec_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:53.533021+00:00
-- url     : https://prove2.me/submissions/45f44948-02a4-48be-9f6c-710fc57e0b47

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
theorem _root_.solution {N : ℕ} (LL : M.Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by
  simp [M.Letters.snoc]
end Formalism.GM.FrozenVariableLemmas
