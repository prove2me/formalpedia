-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.prod_blockEmb_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:58.11603+00:00
-- url     : https://prove2.me/submissions/31de4db8-fcc0-4d02-9e93-ad6714166617

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_prod_monomial_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (p : S → (Fin k × Fin n →₀ ℕ)) (a : S → K) :
    ∏ s, blockEmb K s (monomial (p s) (a s)) = monomial (glue p) (∏ s, a s) := by
  simp only [blockEmb, rename_monomial]
  exact prod_monomial_eq _ _ _
end Formalism.L2.G.Model.TS
