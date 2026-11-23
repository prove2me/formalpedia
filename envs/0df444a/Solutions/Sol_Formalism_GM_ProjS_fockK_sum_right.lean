-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:09.689545+00:00
-- url     : https://prove2.me/submissions/4430a645-13c3-4de3-a630-acb496992565

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_symm
import Theorems.Thm_Formalism_GM_ProjS_fockK_sum_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ k) (F : MvPolynomial σ k) :
    M.fockK F (∑ i ∈ s, f i) = ∑ i ∈ s, M.fockK F (f i) := by
  rw [fockK_symm F, fockK_sum_left]
  exact Finset.sum_congr rfl (fun i _ => fockK_symm _ _)
end Formalism.GM.ProjS
