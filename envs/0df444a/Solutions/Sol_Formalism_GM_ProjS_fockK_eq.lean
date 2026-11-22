-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:37.393144+00:00
-- url     : https://prove2.me/submissions/2b8f99c2-7965-49a9-94c6-7d87ac22df33

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

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
theorem _root_.solution (F G : MvPolynomial σ k) :
    M.fockK F G = ∑ m ∈ F.support, F.coeff m * G.coeff m * mfac m := rfl
end Formalism.GM.ProjS
