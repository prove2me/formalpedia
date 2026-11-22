-- Prove2me | solution 1 for Formalism.GM.FockB.eulL_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:16.379223+00:00
-- url     : https://prove2.me/submissions/5e01bc6e-bba3-49b2-a798-ebaf5acadda3

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_mulLeftX_mem
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem

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
theorem _root_.solution {s : ℕ} {S : Set σ} (t : Fin s → σ) (ht : ∀ c, t c ∈ S) :
    (ProjS.eulL t : Module.End k (MvPolynomial σ k)) ∈ Ops S := by
  unfold ProjS.eulL
  refine sum_mem fun c _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (mulLeftX_mem (ht c)) (pderiv_mem (ht c))
end Formalism.GM.FockB
