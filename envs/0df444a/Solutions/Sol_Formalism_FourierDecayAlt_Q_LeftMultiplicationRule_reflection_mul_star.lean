-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.reflection_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:17.356034+00:00
-- url     : https://prove2.me/submissions/a63c4549-4386-48de-b9d2-ae663024e1ae

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_off_support
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_isotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_dual_isotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c * w1 k r l (star c) = 1 := by
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [Finset.sum_eq_single (esI k r l)]
    · rw [reflection_column_isotropic, if_pos rfl, reflection_column_dual_isotropic]
      by_cases hp : p = eI k r l
      · rw [if_pos hp, if_pos hp, inv_mul_cancel₀ hsc]
      · rw [if_neg hp, if_neg hp, zero_mul]
    · intro t _ ht; rw [reflection_column_isotropic, if_neg ht, mul_zero]
    · simp
  · by_cases hq2 : q = esI k r l
    · subst hq2
      rw [Finset.sum_eq_single (eI k r l)]
      · rw [reflection_column_dual_isotropic, if_pos rfl, reflection_column_isotropic, star_star]
        by_cases hp : p = esI k r l
        · rw [if_pos hp, if_pos hp, mul_inv_cancel₀ hc]
        · rw [if_neg hp, if_neg hp, zero_mul]
      · intro t _ ht; rw [reflection_column_dual_isotropic, if_neg ht, mul_zero]
      · simp
    · rw [Finset.sum_eq_single q]
      · rw [reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one, reflection_off_support _ _ p q hq1 hq2]
      · intro t _ ht; rw [reflection_off_support _ _ t q hq1 hq2, if_neg ht, mul_zero]
      · simp
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
