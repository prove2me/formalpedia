-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_tieE_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:28.066877+00:00
-- url     : https://prove2.me/submissions/8dc7f60d-a476-4bcf-8403-a567031a039c

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE

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
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (l : ℕ) (g h : MvPolynomial σ k) :
    M.fockK ((tieE w e ^ l) g) h = M.fockK g ((tieF w e ^ l) h) := by
  induction l generalizing h with
  | zero => simp
  | succ l ih =>
    rw [pow_succ' (Formalism.GM.tieE w e) l, Module.End.mul_apply, fockK_tieE, ih, pow_succ (Formalism.GM.tieF w e) l,
      Module.End.mul_apply]
end Formalism.GM.ProjS
