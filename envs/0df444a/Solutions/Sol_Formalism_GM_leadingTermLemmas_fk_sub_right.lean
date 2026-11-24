-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:02.887646+00:00
-- url     : https://prove2.me/submissions/1d3aa847-20a0-4ce8-a25b-9838bf974449

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_symm
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sub_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (F G G' : MvPolynomial σ K) : fk F (G - G') = fk F G - fk F G' := by
  rw [fk_symm, fk_sub_left, fk_symm G, fk_symm G']
end Formalism.GM.leadingTermLemmas
