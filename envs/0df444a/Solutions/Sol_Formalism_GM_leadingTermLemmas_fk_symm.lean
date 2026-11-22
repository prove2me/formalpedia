-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:02.020598+00:00
-- url     : https://prove2.me/submissions/7aab2c5a-60a4-4ef0-b204-67e9638cac39

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
theorem _root_.solution (F G : MvPolynomial σ K) : fk F G = fk G F := by
  rw [fk_eq_sum F G _ (Finset.subset_union_left (s₂ := G.support)),
    fk_eq_sum G F _ (Finset.subset_union_right (s₁ := F.support))]
  exact Finset.sum_congr rfl (fun m _ => by ring)
end Formalism.GM.leadingTermLemmas
