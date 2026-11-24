-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.mul_weyl_cell_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:13.432983+00:00
-- url     : https://prove2.me/submissions/45f4bab3-61ba-435c-9183-541b08072eef

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_off_support
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_off_support_row

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
    (h1 : A p (eI k r l) = 0) (h2 : A p (esI k r l) = 0) : (A * w1 k r l c) p q = A p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · by_cases hq1 : q = eI k r l
    · subst hq1; rw [h1, zero_mul]
    · by_cases hq2 : q = esI k r l
      · subst hq2; rw [h2, zero_mul]
      · rw [reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one]
  · intro t _ ht
    by_cases ht1 : t = eI k r l
    · subst ht1; rw [h1, zero_mul]
    · by_cases ht2 : t = esI k r l
      · subst ht2; rw [h2, zero_mul]
      · rw [reflection_off_support_row _ _ t q ht1 ht2, if_neg ht, mul_zero]
  · simp
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
