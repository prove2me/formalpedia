-- Prove2me | solution 1 for Formalism.GM.FockB.tieEh_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:23.668551+00:00
-- url     : https://prove2.me/submissions/2273e74e-77c8-4886-906e-c5fc9c26c670

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_tieEh_eq_mulLeft

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
theorem _root_.solution (j : ℕ) (u : MvPolynomial σ k) :
    (M.tieEh w e zv sv ^ j) u = Ehp w e zv sv ^ j * u := by
  rw [tieEh_eq_mulLeft, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
end Formalism.GM.FockB
