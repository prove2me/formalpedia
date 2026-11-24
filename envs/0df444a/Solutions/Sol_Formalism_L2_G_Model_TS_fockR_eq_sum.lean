-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:14.677464+00:00
-- url     : https://prove2.me/submissions/65b00544-187e-4b11-955c-86e1132c5e7a

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
variable {σ R : Type*} [CommRing R]
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]
end Formalism.L2.G.Model.TS
