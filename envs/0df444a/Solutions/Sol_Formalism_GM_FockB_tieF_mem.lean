-- Prove2me | solution 1 for Formalism.GM.FockB.tieF_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:12.410133+00:00
-- url     : https://prove2.me/submissions/4d6ef2b6-32bf-42e0-9704-9ae2974c1713

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_GM_FockB_w_mem
import Theorems.Thm_Formalism_GM_FockB_e_mem

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
theorem _root_.solution : (Formalism.GM.tieF w e : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  unfold Formalism.GM.tieF
  refine sum_mem fun c _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (pderiv_mem (w_mem c)) (pderiv_mem (e_mem c))
end Formalism.GM.FockB
