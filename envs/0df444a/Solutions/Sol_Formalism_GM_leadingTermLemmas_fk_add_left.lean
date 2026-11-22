-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:53.547989+00:00
-- url     : https://prove2.me/submissions/b913cf1e-29df-4bc4-8c76-2bd93205dca2

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
theorem _root_.solution (F F' G : MvPolynomial σ K) : fk (F + F') G = fk F G + fk F' G := by
  rw [fk_eq_sum (F + F') G (F.support ∪ F'.support) support_add,
    fk_eq_sum F G _ (Finset.subset_union_left (s₂ := F'.support)),
    fk_eq_sum F' G _ (Finset.subset_union_right (s₁ := F.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_add]; ring)
end Formalism.GM.leadingTermLemmas
