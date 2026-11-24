-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.mul_apply_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:40:22.149107+00:00
-- url     : https://prove2.me/submissions/1030b390-b196-4ede-b775-02c3fe3ab61a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS

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
theorem _root_.solution {l : Fin r} {M N : Mx k r} (hM : InS k r l M) (hN : InS k r l N)
    (p q : Fin (2 * r + k + 1)) (h : ¬ (p.val = l.val ∧ q.val = 2 * r + k - l.val)) :
    (M * N) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h1 : SP k r l p j
  · by_cases h2 : SP k r l j q
    · exfalso
      unfold SP at h1 h2
      have := l.isLt
      omega
    · rw [hN j q h2, mul_zero]
  · rw [hM p j h1, zero_mul]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
