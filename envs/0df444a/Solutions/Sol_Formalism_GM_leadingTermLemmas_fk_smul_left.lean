-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:04.808093+00:00
-- url     : https://prove2.me/submissions/dce0f57e-8736-4d81-943e-0e0706be7442

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_eq_sum

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
theorem _root_.solution (c : K) (F G : MvPolynomial σ K) : fk (c • F) G = c * fk F G := by
  rw [fk_eq_sum (c • F) G F.support support_smul, fk, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_smul, smul_eq_mul]; ring)
end Formalism.GM.leadingTermLemmas
