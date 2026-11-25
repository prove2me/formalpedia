-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:01:26.449923+00:00
-- url     : https://prove2.me/submissions/1af43117-bcba-4395-8244-ae95368a992f

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    ell k r z (A - B) = ell k r z A - ell k r z B := by
  unfold ell
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [Matrix.sub_mulVec]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
