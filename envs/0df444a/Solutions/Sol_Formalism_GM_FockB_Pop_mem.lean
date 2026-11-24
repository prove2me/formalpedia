-- Prove2me | solution 1 for Formalism.GM.FockB.Pop_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:09.621113+00:00
-- url     : https://prove2.me/submissions/a410dbc0-9c92-4408-ac80-70bff53682e0

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_zv_mem
import Theorems.Thm_Formalism_GM_FockB_X_mem
import Theorems.Thm_Formalism_GM_FockB_tieEh_mem
import Theorems.Thm_Formalism_GM_FockB_tieF_mem

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
theorem _root_.solution (o n z : ℕ) : (Pop w e zv sv o n z : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  unfold Pop
  refine sum_mem fun l _ => Subalgebra.smul_mem _ ?_ _
  exact mul_mem (mul_mem (pow_mem tieEh_mem _) (pow_mem tieF_mem _))
    (mulLeft_mem (pow_mem (X_mem zv_mem) _))
end Formalism.GM.FockB
