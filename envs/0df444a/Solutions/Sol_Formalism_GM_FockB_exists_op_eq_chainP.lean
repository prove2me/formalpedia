-- Prove2me | solution 1 for Formalism.GM.FockB.exists_op_eq_chainP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:13.705387+00:00
-- url     : https://prove2.me/submissions/1fb9b461-0278-4838-b472-d76a11cf3090

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_mono
import Theorems.Thm_Formalism_GM_FockB_Pop_mem
import Theorems.Thm_Formalism_GM_FockB_tieP_eq_Pop
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
    ∃ T ∈ Ops (k := k) (VL w e zv sv L), ∀ y, chainP w e zv sv z o n L y = T y := by
  induction L with
  | nil => exact ⟨1, one_mem _, fun y => rfl⟩
  | cons a L ih =>
    obtain ⟨T, hT, hTe⟩ := ih
    refine ⟨Pop (w a) (e a) (zv a) (sv a) (o a) (n a) (z a) * T,
      mul_mem (ops_mono (Va_sub (List.mem_cons_self ..)) (Pop_mem _ _ _)) (ops_mono VL_cons_sub hT), fun y => ?_⟩
    show M.tieP _ _ _ _ _ _ _ (chainP w e zv sv z o n L y) = _
    rw [hTe, tieP_eq_Pop, Module.End.mul_apply]
end Formalism.GM.FockB
