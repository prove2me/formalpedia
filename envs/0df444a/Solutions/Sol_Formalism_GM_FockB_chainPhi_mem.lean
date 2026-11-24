-- Prove2me | solution 1 for Formalism.GM.FockB.chainPhi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:40.735933+00:00
-- url     : https://prove2.me/submissions/10de1575-f684-4b1c-8fbd-4b26a86d6b1d

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_mono
import Theorems.Thm_Formalism_GM_FockB_tiePhi_mem
import Theorems.Thm_Formalism_GM_FockB_Va_sub
import Theorems.Thm_Formalism_GM_FockB_VL_cons_sub

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
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)
variable {w e zv sv z}
namespace Formalism.GM.FockB
theorem _root_.solution (o n : α → ℕ) (L : List α) :
    (chainPhi w e z o n L : Module.End k (MvPolynomial σ k)) ∈ Ops (VL w e zv sv L) := by
  induction L with
  | nil => exact one_mem _
  | cons a L ih =>
    show Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) * chainPhi w e z o n L ∈ _
    exact mul_mem (ops_mono (Va_sub (List.mem_cons_self ..)) (tiePhi_mem (zv := zv a) (sv := sv a) _ _ _))
      (ops_mono VL_cons_sub ih)
end Formalism.GM.FockB
