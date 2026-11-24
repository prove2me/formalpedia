-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:53.136602+00:00
-- url     : https://prove2.me/submissions/77ee614e-50db-4bdf-8a85-fef21b7a4ebb

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_map_wf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (F G : MvPolynomial σ ℚ) : fk (map ι F) (map ι G) = ι (fk F G) := by
  unfold fk
  rw [support_map_of_injective _ (algebraMap ℚ K).injective, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [coeff_map, coeff_map, map_mul, map_mul, map_wf]
end Formalism.GM.leadingTermLemmas
