-- Prove2me | solution 1 for Formalism.GM.FockB.tiePhi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:50.546372+00:00
-- url     : https://prove2.me/submissions/7849d281-93af-429b-ae0c-1df103d22172

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_tieE_mem
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
theorem _root_.solution (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  unfold Formalism.GM.tiePhi
  refine sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (pow_mem tieE_mem _) (pow_mem tieF_mem _)
end Formalism.GM.FockB
