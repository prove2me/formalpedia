-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fock_pairing_row_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:23.019878+00:00
-- url     : https://prove2.me/submissions/698fbd5a-bfa2-419d-b660-ff78aa233a38

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_add_left
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_smul_left
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_sum_left
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_sum_right
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_smul_right
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_monomial_left
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_X_mul
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_rowAct_X
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_coeff_zero
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_chain
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
namespace Formalism.L2.G.Model.TS
theorem _root_.solution : FockRRowAct := by
  intro R _ r n g P
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : rowAct R g (C a : MvPolynomial (Fin r × Fin n) R) = C a := by simp [rowAct]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, tsact_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add, tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, tsact_rowAct_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, tsact_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : rowAct R g p * (C (g v.1 b) * X (b, v.2)) = g v.1 b • (rowAct R g p * X (b, v.2)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]
end Formalism.L2.G.Model.TS
