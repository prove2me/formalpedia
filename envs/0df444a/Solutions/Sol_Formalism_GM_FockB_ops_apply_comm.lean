-- Prove2me | solution 1 for Formalism.GM.FockB.ops_apply_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:39.336813+00:00
-- url     : https://prove2.me/submissions/c2374a4b-e11d-4e28-bd73-958e002b75f4

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_commute

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
variable {k σ : Type} [Field k]
namespace Formalism.GM.FockB
theorem _root_.solution {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) (hT' : T' ∈ Ops S') (y : MvPolynomial σ k) : T (T' y) = T' (T y) := by
  have := (ops_commute hS hT hT').eq
  exact LinearMap.congr_fun this y
end Formalism.GM.FockB
