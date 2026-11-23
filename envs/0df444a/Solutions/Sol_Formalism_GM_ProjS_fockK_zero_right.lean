-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:29.889832+00:00
-- url     : https://prove2.me/submissions/cae85190-84dc-4330-9c73-3a05b3ebefa2

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_symm
import Theorems.Thm_Formalism_GM_ProjS_fockK_zero_left

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
theorem _root_.solution (F : MvPolynomial σ k) : M.fockK F 0 = 0 := by
  rw [fockK_symm, fockK_zero_left]
end Formalism.GM.ProjS
