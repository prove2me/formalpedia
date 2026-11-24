-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:10.828216+00:00
-- url     : https://prove2.me/submissions/5225196f-aed4-41b7-aed0-4e54792d5382

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
theorem _root_.solution (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  classical
  rw [fockR_eq_sum _ _ f.support (MvPolynomial.support_smul), fockR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_smul, smul_eq_mul]; ring
end Formalism.L2.G.Model.TS
