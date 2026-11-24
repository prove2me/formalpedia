-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:27.712204+00:00
-- url     : https://prove2.me/submissions/57cce6ab-5e18-4668-ad3b-59bb67d1c219

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_single
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_posL_val

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
    Pat k r l (Matrix.single (eI k r l) (posL k r l.succ j) 1) := by
  have h := posL_val (k := k) l j
  apply pat_single
  left
  exact ⟨rfl, by omega, by omega⟩
end Formalism.FourierDecayAlt.Q.QRR
