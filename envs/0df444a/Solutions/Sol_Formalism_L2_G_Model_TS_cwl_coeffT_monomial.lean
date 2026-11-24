-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cwl_coeffT_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:49.160464+00:00
-- url     : https://prove2.me/submissions/39f9d49f-9cba-4a3f-a2f7-486a317ab1f4

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeff_coeffT
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
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (d u : Fin r × Fin n →₀ ℕ) (c : MvPolynomial (Fin r × Fin n) R) :
    cwl_coeffT d (monomial u c) = monomial u (coeff d c) := by
  classical
  ext m
  rw [cwl_coeff_coeffT, coeff_monomial, coeff_monomial]
  split_ifs <;> simp
end Formalism.L2.G.Model.TS
