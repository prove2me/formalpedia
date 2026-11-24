-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:50.344325+00:00
-- url     : https://prove2.me/submissions/d61d93e5-ead5-441f-a4e2-609e20bc1574

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_symm
import Theorems.Thm_Formalism_GM_ProjS_fockK_add_left

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
theorem _root_.solution (F G G' : MvPolynomial σ k) :
    M.fockK F (G + G') = M.fockK F G + M.fockK F G' := by
  rw [fockK_symm F (G + G'), fockK_add_left, fockK_symm G F, fockK_symm G' F]
end Formalism.GM.ProjS
