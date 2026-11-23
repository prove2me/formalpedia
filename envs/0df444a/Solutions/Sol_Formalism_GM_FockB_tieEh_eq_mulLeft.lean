-- Prove2me | solution 1 for Formalism.GM.FockB.tieEh_eq_mulLeft
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:59.4589+00:00
-- url     : https://prove2.me/submissions/23a1e36d-69a5-4732-bcd5-e0cc7d90d3f7

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
theorem _root_.solution : (M.tieEh w e zv sv : Module.End k (MvPolynomial σ k)) =
    LinearMap.mulLeft k (Ehp w e zv sv) := rfl
end Formalism.GM.FockB
