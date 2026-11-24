-- Prove2me | solution 1 for Formalism.GM.FockB.chain_rw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:57.6217+00:00
-- url     : https://prove2.me/submissions/919d1125-cf26-49a3-b772-84da05a14ee0

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
import Theorems.Thm_Formalism_GM_FockB_Pop_mem
import Theorems.Thm_Formalism_GM_FockB_tieP_eq_Pop
import Theorems.Thm_Formalism_GM_FockB_chainE_mem

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
theorem _root_.solution (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    (Y0 : MvPolynomial σ k) :
    chainE w e zv sv j (a :: L) * chainP w e zv sv z o n (a :: L) Y0 =
      Ehp (w a) (e a) (zv a) (sv a) ^ j a * M.tieP (w a) (e a) (zv a) (sv a) (o a) (n a) (z a)
        (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) := by
  have hHm := mulLeft_mem (chainE_mem (w := w) (e := e) (zv := zv) (sv := sv) (k := k) j L)
  have hPa := Pop_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) (o a) (n a) (z a)
  show (Ehp (w a) (e a) (zv a) (sv a) ^ j a * chainE w e zv sv j L) *
    M.tieP _ _ _ _ _ _ _ (chainP w e zv sv z o n L Y0) = _
  rw [mul_assoc, tieP_eq_Pop, tieP_eq_Pop]
  congr 1
  exact (ops_apply_comm hdisj hPa hHm _).symm
end Formalism.GM.FockB
