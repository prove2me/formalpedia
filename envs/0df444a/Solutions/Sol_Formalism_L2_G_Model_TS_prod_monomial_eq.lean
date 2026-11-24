-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.prod_monomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:46.301561+00:00
-- url     : https://prove2.me/submissions/3aba14df-5919-457c-91e2-f27360cb704b

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
theorem _root_.solution {ι τ : Type*} (t : Finset ι) (e : ι → τ →₀ ℕ) (a : ι → K) :
    ∏ i ∈ t, monomial (e i) (a i) = monomial (∑ i ∈ t, e i) (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]
end Formalism.L2.G.Model.TS
