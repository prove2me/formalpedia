-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.tsact_fact_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:00:51.091325+00:00
-- url     : https://prove2.me/submissions/a2a24f31-7ac2-45c6-9ac9-1eae19b4e2ec

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
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
variable {σ R : Type*} [CommRing R]
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (m : σ →₀ ℕ) (s : Finset σ) (h : m.support ⊆ s) :
    ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ s, (m k).factorial := by
  refine Finset.prod_subset h fun k _ hk => ?_
  have h0 : m k = 0 := by simpa using hk
  rw [h0, Nat.factorial_zero]
end Formalism.L2.G.Model.TS
