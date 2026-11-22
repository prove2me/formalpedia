-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:03.351221+00:00
-- url     : https://prove2.me/submissions/5516b8cc-4c3a-4ee0-85e0-46e25ad10372

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_superset

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
theorem _root_.solution (F G : MvPolynomial σ k) : M.fockK F G = M.fockK G F := by
  classical
  rw [fockK_superset F G (F.support ∪ G.support) (fun x hx => Finset.mem_union_left _ hx),
    fockK_superset G F (F.support ∪ G.support) (fun x hx => Finset.mem_union_right _ hx)]
  exact Finset.sum_congr rfl (fun m _ => by ring)
end Formalism.GM.ProjS
