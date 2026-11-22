-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:13.581349+00:00
-- url     : https://prove2.me/submissions/cd8c04d9-2268-4197-89de-1f049964ba7b

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_symm
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_left

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
theorem _root_.solution (c : k) (F G : MvPolynomial σ k) :
    M.fockK F (c • G) = c * M.fockK F G := by
  rw [fockK_symm F (c • G), fockK_smul_left, fockK_symm G F]
end Formalism.GM.ProjS
