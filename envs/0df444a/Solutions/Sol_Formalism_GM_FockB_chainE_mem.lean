-- Prove2me | solution 1 for Formalism.GM.FockB.chainE_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:46.1758+00:00
-- url     : https://prove2.me/submissions/aa71c1a7-9614-4c29-8424-00eb9debba84

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_Ehp_mem
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
theorem _root_.solution (j : α → ℕ) (L : List α) :
    (chainE w e zv sv j L : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' VL w e zv sv L) := by
  induction L with
  | nil => simp only [chainE, List.map_nil, List.prod_nil]; exact one_mem _
  | cons a L ih =>
    simp only [chainE, List.map_cons, List.prod_cons]
    exact mul_mem (pow_mem (Algebra.adjoin_mono (Set.image_mono (Va_sub (List.mem_cons_self ..))) Ehp_mem) _)
      (Algebra.adjoin_mono (Set.image_mono VL_cons_sub) ih)
end Formalism.GM.FockB
