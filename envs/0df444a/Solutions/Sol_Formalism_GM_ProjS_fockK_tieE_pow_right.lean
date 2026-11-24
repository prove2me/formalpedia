-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_tieE_pow_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:17.41626+00:00
-- url     : https://prove2.me/submissions/821f779b-1c18-4bf6-9d05-5fabe58f8643

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_symm
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow

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
    M.fockK g ((tieE w e ^ l) h) = M.fockK ((tieF w e ^ l) g) h := by
  rw [fockK_symm g, fockK_tieE_pow, fockK_symm h]
end Formalism.GM.ProjS
