-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_weightSp_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:44:40.257144+00:00
-- url     : https://prove2.me/submissions/bb4c2951-f102-41a5-b92b-bd16696663be

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_coeff_E
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_weightSp

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
theorem _root_.solution (n : ℕ) (w : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ weightSp (glOps ℚ n (rowLetters n) Set.univ) w) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m ≠ w) :
    coeff m z = 0 := by
  rw [qn_mem_weightSp] at hz
  by_contra hne
  apply hm
  funext a
  have h := congrArg (coeff m) (hz a)
  rw [qn_coeff_E, coeff_smul, smul_eq_mul] at h
  have := mul_right_cancel₀ hne h
  exact_mod_cast this
end Formalism.InvariantFactorPaths.ColumnFamilies
