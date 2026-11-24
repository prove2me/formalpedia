-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_rowDiv_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:54.081398+00:00
-- url     : https://prove2.me/submissions/68711a1c-2862-4b45-bc56-9c647275d44b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_natsmul
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_deriv_rowGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) (transposeVariables ℚ n f) = rowDiv ℚ a b k (transposeVariables ℚ n (qn_D n a b f)) := by
  unfold rowDiv
  rw [← qn_deriv_rowGen n a b hab f, Polynomial.coeff_derivative, qn_natsmul]
end Formalism.InvariantFactorPaths.ColumnFamilies
