-- Prove2me | solution 1 for Formalism.GM.FockB.Ehp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:23.768327+00:00
-- url     : https://prove2.me/submissions/b17c58dd-52ca-41e3-b070-7fc67fc2bc60

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_w_mem
import Theorems.Thm_Formalism_GM_FockB_e_mem
import Theorems.Thm_Formalism_GM_FockB_zv_mem
import Theorems.Thm_Formalism_GM_FockB_sv_mem
import Theorems.Thm_Formalism_GM_FockB_X_mem

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
theorem _root_.solution : (Ehp w e zv sv : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' V w e zv sv) :=
  add_mem (mul_mem (X_mem zv_mem) (X_mem sv_mem)) (sum_mem fun c _ => mul_mem (X_mem (w_mem c)) (X_mem (e_mem c)))
end Formalism.GM.FockB
