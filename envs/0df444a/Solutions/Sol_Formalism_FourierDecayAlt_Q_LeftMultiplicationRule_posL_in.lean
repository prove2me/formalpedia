-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.posL_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:15.396338+00:00
-- url     : https://prove2.me/submissions/cdc54cfa-5964-4c8e-ba10-3cd76041d1de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule

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
theorem _root_.solution (l : Fin r) (j : Fin (mdim k r l.succ)) :
    l.val < (posL k r l.succ j).val ∧ (posL k r l.succ j).val < 2 * r + k - l.val := by
  have hj := j.isLt
  have hl := l.isLt
  unfold mdim at hj
  show l.val < j.val + l.succ.val ∧ j.val + l.succ.val < 2 * r + k - l.val
  simp only [Fin.val_succ] at hj ⊢
  omega
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
