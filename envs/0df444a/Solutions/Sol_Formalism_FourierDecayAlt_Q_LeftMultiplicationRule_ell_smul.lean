-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:56.294773+00:00
-- url     : https://prove2.me/submissions/135782b2-ea30-4570-8e44-36378134e2a3

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (A : Mx k r) :
    ell k r z (s • A) = s * ell k r z A := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.smul_mulVec]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
