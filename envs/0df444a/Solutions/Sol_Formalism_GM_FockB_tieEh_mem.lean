-- Prove2me | solution 1 for Formalism.GM.FockB.tieEh_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:06.620208+00:00
-- url     : https://prove2.me/submissions/c95849a8-5f3d-4420-a2b9-b81e090fe3be

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_Ehp_mem
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
theorem _root_.solution : (M.tieEh w e zv sv : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  rw [tieEh_eq_mulLeft]; exact mulLeft_mem Ehp_mem
end Formalism.GM.FockB
