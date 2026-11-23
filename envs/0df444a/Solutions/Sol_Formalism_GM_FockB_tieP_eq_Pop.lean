-- Prove2me | solution 1 for Formalism.GM.FockB.tieP_eq_Pop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:36.51184+00:00
-- url     : https://prove2.me/submissions/8931ca78-8f7f-4c47-adf5-67ec454bf02f

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

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
theorem _root_.solution (o n z : ℕ) (y : MvPolynomial σ k) :
    M.tieP w e zv sv o n z y = Pop w e zv sv o n z y := by
  simp [M.tieP, Pop, LinearMap.sum_apply, Module.End.mul_apply]
end Formalism.GM.FockB
