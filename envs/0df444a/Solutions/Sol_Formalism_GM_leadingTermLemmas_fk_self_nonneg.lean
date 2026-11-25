-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_self_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:19.17626+00:00
-- url     : https://prove2.me/submissions/3cb75f99-3e2f-4f08-849f-6e0795567fd2

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wf_pos

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (F : MvPolynomial σ ℝ) : 0 ≤ fk F F :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (mul_self_nonneg _) (wf_pos m).le)
end Formalism.GM.leadingTermLemmas
