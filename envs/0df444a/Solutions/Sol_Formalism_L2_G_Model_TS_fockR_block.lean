-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:28.2558+00:00
-- url     : https://prove2.me/submissions/9620254a-32d7-4320-a89d-e5a014179fad

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_sum_left
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_sum_right
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_monomial
import Theorems.Thm_Formalism_L2_G_Model_TS_glue_injective
import Theorems.Thm_Formalism_L2_G_Model_TS_glue_fact
import Theorems.Thm_Formalism_L2_G_Model_TS_prod_blockEmb_expand
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_expand
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
theorem _root_.solution (F G : S → MvPolynomial (Fin k × Fin n) K) :
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s) := by
  classical
  rw [prod_blockEmb_expand F, prod_blockEmb_expand G, fockR_sum_left]
  simp_rw [fockR_sum_right, fockR_expand (F _) (G _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [fockR_monomial]
  by_cases h : p = q
  · subst h
    simp only [if_true, glue_fact, Finset.prod_mul_distrib, Nat.cast_prod]
  · have h' : glue p ≠ glue q := fun e => h (glue_injective e)
    rw [if_neg h']
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm
end Formalism.L2.G.Model.TS
