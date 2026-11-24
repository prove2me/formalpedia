-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_P_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:54.853087+00:00
-- url     : https://prove2.me/submissions/1237b56d-318f-4b23-a597-08ceb9b6d564

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_left
import Theorems.Thm_Formalism_GM_ProjS_fockK_sum_left
import Theorems.Thm_Formalism_GM_ProjS_fockK_zero_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow
import Theorems.Thm_Formalism_GM_ProjS_tieP_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (o n z : ℕ) (y Q : MvPolynomial σ k)
    (hQ : tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) Q = 0) :
    M.fockK (M.tieP w e zv sv o n z y) Q = M.fockK (X zv ^ z * y) Q := by
  rw [tieP_eq, fockK_sum_left, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
  · simp
  · intro i _
    rw [fockK_smul_left, fockK_tieE_pow,
      pow_succ (Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)) i, Module.End.mul_apply, hQ,
      map_zero, fockK_zero_right, mul_zero]
end Formalism.GM.ProjS
