-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.weyl_cell_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:18.803736+00:00
-- url     : https://prove2.me/submissions/8c44b4f2-60cf-4f64-927a-36d57e655668

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_off_support

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
theorem _root_.solution (l : Fin r) (c : ℂ) (A : Mx k r) (p q : Fin (2 * r + k + 1))
    (h1 : A (eI k r l) q = 0) (h2 : A (esI k r l) q = 0) : (w1 k r l c * A) p q = A p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · by_cases hp1 : p = eI k r l
    · subst hp1; rw [h1, mul_zero]
    · by_cases hp2 : p = esI k r l
      · subst hp2; rw [h2, mul_zero]
      · rw [reflection_off_support _ _ p p hp1 hp2, if_pos rfl, one_mul]
  · intro t _ ht
    by_cases ht1 : t = eI k r l
    · subst ht1; rw [h1, mul_zero]
    · by_cases ht2 : t = esI k r l
      · subst ht2; rw [h2, mul_zero]
      · rw [reflection_off_support _ _ p t ht1 ht2, if_neg (Ne.symm ht), zero_mul]
  · simp
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
