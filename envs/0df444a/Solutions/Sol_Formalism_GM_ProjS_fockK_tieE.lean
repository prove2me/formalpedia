-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_tieE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:43.841797+00:00
-- url     : https://prove2.me/submissions/7d92bc54-aed1-4fc3-96c9-f2a85592d514

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_sum_left
import Theorems.Thm_Formalism_GM_ProjS_fockK_sum_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_X_mul
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1


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
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (g h : MvPolynomial σ k) :
    M.fockK (tieE w e g) h = M.fockK g (tieF w e h) := by
  rw [Formalism.GM.tieE_apply', Finset.sum_mul, fockK_sum_left, Formalism.GM.tieF_apply', fockK_sum_right]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [mul_assoc, fockK_X_mul, fockK_X_mul, pderiv_comm]
end Formalism.GM.ProjS
