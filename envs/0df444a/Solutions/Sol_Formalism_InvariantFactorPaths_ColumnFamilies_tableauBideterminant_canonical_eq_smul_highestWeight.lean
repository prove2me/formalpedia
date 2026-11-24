-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.tableauBideterminant_canonical_eq_smul_highestWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:12.352377+00:00
-- url     : https://prove2.me/submissions/e402062c-d4d8-4e1e-83f9-822c7461f659

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_nu_anti
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_canonical_eq_prod_leadingMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_eval_idPoint_lpMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_lpMinor
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
theorem _root_.solution (mu : Fin n → ℤ) : ∃ c0 : ℚ, c0 ≠ 0 ∧ qd_P mu (canT mu) = c0 • hw ℚ le_rfl (qd_nu mu) := by
  obtain ⟨c0, h0⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ (tableauBideterminant_mem_dualWeyl' mu (canT mu)) (by
    intro a b hab k hk
    unfold rowDiv
    rw [tableauBideterminant_canonical_eq_prod_leadingMinor, map_prod]
    simp only [rowGen_lpMinor ℚ a b hab]
    rw [← map_prod, Polynomial.coeff_C, if_neg (by omega)])
  refine ⟨c0, ?_, h0⟩
  rintro rfl
  rw [zero_smul, tableauBideterminant_canonical_eq_prod_leadingMinor] at h0
  have := congrArg (eval (idPoint ℚ n n)) h0
  simp [eval_idPoint_lpMinor] at this
end Formalism.InvariantFactorPaths.ColumnFamilies
