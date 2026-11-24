-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:13.345985+00:00
-- url     : https://prove2.me/submissions/288fecef-5b63-4168-9a5a-9c9e75671b38

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_coeff_X_pderiv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_D_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_E_eq
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (glOps ℚ n (rowLetters n) Set.univ a a f) = (qn_wt m a : ℚ) * coeff m f := by
  rw [qn_E_eq, qn_D_apply, coeff_sum]
  simp only [qn_coeff_X_pderiv]
  rw [← Finset.sum_mul]
  simp [qn_wt]
end Formalism.InvariantFactorPaths.ColumnFamilies
