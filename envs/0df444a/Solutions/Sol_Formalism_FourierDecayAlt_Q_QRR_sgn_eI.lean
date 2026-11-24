-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.sgn_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:52:00.191804+00:00
-- url     : https://prove2.me/submissions/d910c940-74dd-49fc-85d0-a7733734405a

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
theorem _root_.solution (l : Fin r) : WeylGroupFacts.sgn k r (eI k r l) = 1 := by
  have hl := l.isLt
  unfold WeylGroupFacts.sgn
  rw [if_neg]
  simp only [eI]
  omega
end Formalism.FourierDecayAlt.Q.QRR
