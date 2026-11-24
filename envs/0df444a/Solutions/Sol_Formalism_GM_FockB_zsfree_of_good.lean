-- Prove2me | solution 1 for Formalism.GM.FockB.zsfree_of_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:10.295835+00:00
-- url     : https://prove2.me/submissions/aa2863ba-08b4-4834-9c91-3346ebb59eec

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_free_of_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.FockB
theorem _root_.solution [CharZero k] {o n : ℕ} {y : MvPolynomial σ k} (h : Good w e zv sv o n y) :
    M.ZSFree zv sv y :=
  fun m hm => ⟨free_of_pderiv h.2.2.1 m hm, free_of_pderiv h.2.2.2 m hm⟩
end Formalism.GM.FockB
