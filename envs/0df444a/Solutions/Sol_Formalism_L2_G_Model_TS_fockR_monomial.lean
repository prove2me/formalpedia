-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:05.243477+00:00
-- url     : https://prove2.me/submissions/de21385a-bb93-4a94-b23b-d345388724b1

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_eq_sum
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
theorem _root_.solution [DecidableEq (σ →₀ ℕ)] (m m' : σ →₀ ℕ) (a b : R) :
    fockR (monomial m a) (monomial m' b) =
      if m = m' then a * b * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) else 0 := by
  classical
  rw [fockR_eq_sum _ _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  by_cases h : m = m'
  · subst h; simp
  · have h' : ¬ m' = m := fun e => h e.symm
    simp [h, h']
end Formalism.L2.G.Model.TS
