-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.glue_fact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:15.431707+00:00
-- url     : https://prove2.me/submissions/bddb74fc-e835-449f-a35e-978c2f937119

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_glue_apply
import Theorems.Thm_Formalism_L2_G_Model_TS_fact_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (p : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ x ∈ (glue p).support, (glue p x).factorial = ∏ s, ∏ v ∈ (p s).support, (p s v).factorial := by
  rw [fact_univ, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [fact_univ]
  exact Finset.prod_congr rfl fun v _ => by rw [glue_apply]
end Formalism.L2.G.Model.TS
