-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.posL_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:08.231837+00:00
-- url     : https://prove2.me/submissions/9fb6587d-58c2-4001-9945-ee3b0c2e2e43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (l : Fin r) (j : Fin (mdim k r l.succ)) :
    (posL k r l.succ j).val = j.val + (l.val + 1) ∧ j.val + (l.val + 1) < 2 * r + k - l.val := by
  have hj : j.val < 2 * (r - (l.val + 1)) + k + 1 := j.isLt
  have hl := l.isLt
  refine ⟨rfl, ?_⟩
  show j.val + (l.val + 1) < 2 * r + k - l.val
  omega
end Formalism.FourierDecayAlt.Q.QRR
