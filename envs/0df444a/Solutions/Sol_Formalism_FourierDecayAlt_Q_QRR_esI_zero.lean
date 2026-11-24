-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.esI_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:11:11.131028+00:00
-- url     : https://prove2.me/submissions/6f020d4b-5274-4c37-b7e1-42392b87e6f2

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) : z (esI k r l) = 0 := by
  have hl := l.isLt
  exact hz _ (Or.inr (show r + k < 2 * r + k - l.val by omega))
end Formalism.FourierDecayAlt.Q.QRR
