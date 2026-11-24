-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:56.801361+00:00
-- url     : https://prove2.me/submissions/41b632b4-dc9e-46d0-80de-ed7c21ace78c

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_add_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_neg_left

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
theorem _root_.solution (F F' G : MvPolynomial σ K) : fk (F - F') G = fk F G - fk F' G := by
  rw [sub_eq_add_neg, fk_add_left, fk_neg_left]; ring
end Formalism.GM.leadingTermLemmas
