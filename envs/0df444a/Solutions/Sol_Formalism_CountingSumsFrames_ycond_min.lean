-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ycond_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:47.431824+00:00
-- url     : https://prove2.me/submissions/a2ee095a-5815-4c3c-86e6-5bff04af8e96

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_min
import Theorems.Thm_Formalism_CountingSumsFrames_wt_min

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) LL j Mt = YCond p (r := r) LL (min j N) Mt := by
  unfold YCond GlStable
  have h1 : glAct p (r := r) LL j = glAct p LL (min j N) := funext fun c => funext fun d => glAct_min LL j c d
  rw [h1, wt_min LL j 0]
end Formalism.CountingSumsFrames
