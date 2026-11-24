-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.cube_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:29.044846+00:00
-- url     : https://prove2.me/submissions/8e4ff5db-58f8-42f8-ba22-c9c3592922fe

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_mul_apply_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {l : Fin r} {Y : Mx k r} (hY : InS k r l Y) : Y * Y * Y = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h1 : p.val = l.val ∧ j.val = 2 * r + k - l.val
  · have h2 : ¬ SP k r l j q := by
      unfold SP
      have := l.isLt
      omega
    rw [hY j q h2, mul_zero]
  · rw [mul_apply_S hY hY p j h1, zero_mul]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
