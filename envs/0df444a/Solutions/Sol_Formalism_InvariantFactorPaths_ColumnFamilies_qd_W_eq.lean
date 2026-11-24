-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_W_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:45.717864+00:00
-- url     : https://prove2.me/submissions/dc10e325-5ee9-482e-a9d5-951763e6d1ee

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_W_closed
import Theorems.Thm_Formalism_GradedWeylDivisibility_closedEqNabla
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_rowAct_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_nu_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_canonical_eq_smul_highestWeight
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) : translatesSpanCanonical mu = dualWeyl ℚ n n (qd_nu mu) := by
  have hcan : qd_P mu (canT mu) ∈ translatesSpanCanonical mu := by
    apply Submodule.subset_span
    exact ⟨1, by simp, by rw [ldrow_rowAct_one]; rfl⟩
  apply closedEqNabla n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ _ (qd_W_closed mu)
  · obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
    have : hw ℚ le_rfl (qd_nu mu) = c0⁻¹ • qd_P mu (canT mu) := by
      rw [h0, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hcan
  · unfold translatesSpanCanonical
    rw [Submodule.span_le]
    rintro _ ⟨g, _, rfl⟩
    exact dualWeylRowStable ℚ n n _ g _ (tableauBideterminant_mem_dualWeyl' mu _)
end Formalism.InvariantFactorPaths.ColumnFamilies
