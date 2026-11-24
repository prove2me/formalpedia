-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fact_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:59:36.437883+00:00
-- url     : https://prove2.me/submissions/acdecb9d-17a3-45ba-b967-cecf203da72b

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
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
theorem _root_.solution {τ : Type*} [Fintype τ] (m : τ →₀ ℕ) :
    ∏ x ∈ m.support, (m x).factorial = ∏ x, (m x).factorial := by
  apply Finset.prod_subset (Finset.subset_univ _)
  intro x _ hx
  simp [Finsupp.notMem_support_iff.mp hx]
end Formalism.L2.G.Model.TS
