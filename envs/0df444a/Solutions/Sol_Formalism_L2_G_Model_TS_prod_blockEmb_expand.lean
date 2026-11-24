-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.prod_blockEmb_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:06.747603+00:00
-- url     : https://prove2.me/submissions/22962fdd-4533-40b5-93bf-39d23e003016

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_prod_blockEmb_monomial

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
theorem _root_.solution [DecidableEq S] (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
      monomial (glue p) (∏ s, coeff (p s) (F s)) := by
  calc ∏ s, blockEmb K s (F s)
      = ∏ s, ∑ m ∈ (F s).support, blockEmb K s (monomial m (coeff m (F s))) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        conv_lhs => rw [(F s).as_sum]
        rw [map_sum]
    _ = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
          ∏ s, blockEmb K s (monomial (p s) (coeff (p s) (F s))) := Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun p _ => prod_blockEmb_monomial _ _
end Formalism.L2.G.Model.TS
