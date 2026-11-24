-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.reflection_fixes_basis_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:16.282833+00:00
-- url     : https://prove2.me/submissions/9eefa520-9c3b-449b-a081-7a48a9313f75

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
theorem _root_.solution (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) (hq1 : q ≠ eI k r l)
    (hq2 : q ≠ esI k r l) : w1 k r l c *ᵥ bvec q = bvec q := by
  funext p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one]
  rw [reflection_off_support _ _ p q hq1 hq2, Pi.single_apply]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
