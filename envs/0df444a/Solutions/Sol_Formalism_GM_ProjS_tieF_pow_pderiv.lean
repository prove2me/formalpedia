-- Prove2me | solution 1 for Formalism.GM.ProjS.tieF_pow_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:33.412033+00:00
-- url     : https://prove2.me/submissions/21cee1dc-1d54-466b-bbf1-feeef122beb1

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_tieF_pderiv

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
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (v : σ) (g : MvPolynomial σ k) (l : ℕ) :
    (tieF w e ^ l) (pderiv v g) = pderiv v ((tieF w e ^ l) g) := by
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [ih, tieF_pderiv]
end Formalism.GM.ProjS
