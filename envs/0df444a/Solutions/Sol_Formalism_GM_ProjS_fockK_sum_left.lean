-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:18.122618+00:00
-- url     : https://prove2.me/submissions/2c26f159-3c3e-4a91-a367-ad9e899240b5

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_add_left
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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ k) (G : MvPolynomial σ k) :
    M.fockK (∑ i ∈ s, f i) G = ∑ i ∈ s, M.fockK (f i) G := by
  classical
  refine Finset.induction_on s (by simp [fockK_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, fockK_add_left, ih]
end Formalism.GM.ProjS
