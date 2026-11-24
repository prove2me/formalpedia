-- Prove2me | solution 1 for Formalism.GM.ProjS.tieF_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:12.55107+00:00
-- url     : https://prove2.me/submissions/11ff10bf-1a73-43ce-a97a-899248fc3744

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
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
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (v : σ) (g : MvPolynomial σ k) :
    tieF w e (pderiv v g) = pderiv v (tieF w e g) := by
  simp only [Formalism.GM.tieF_apply', map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_comm (e c) v, pderiv_comm (w c) v]
end Formalism.GM.ProjS
