-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_ees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:13.73617+00:00
-- url     : https://prove2.me/submissions/41f25d34-913f-432e-ab78-5c4fa8a1066e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_single

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
theorem _root_.solution (l : Fin r) : Pat k r l (Matrix.single (eI k r l) (esI k r l) 1) := by
  have hl := l.isLt
  apply pat_single
  left
  exact ⟨rfl, show l.val < 2 * r + k - l.val by omega, le_refl _⟩
end Formalism.FourierDecayAlt.Q.QRR
