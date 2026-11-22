-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:37.614854+00:00
-- url     : https://prove2.me/submissions/7e5563cb-96f2-45d5-96ca-5f918e8c32c6

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_symm
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sum_left

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
theorem _root_.solution {ι : Type} (t : Finset ι) (F : MvPolynomial σ K) (G : ι → MvPolynomial σ K) :
    fk F (∑ i ∈ t, G i) = ∑ i ∈ t, fk F (G i) := by
  rw [fk_symm, fk_sum_left]; exact Finset.sum_congr rfl (fun i _ => fk_symm _ _)
end Formalism.GM.leadingTermLemmas
