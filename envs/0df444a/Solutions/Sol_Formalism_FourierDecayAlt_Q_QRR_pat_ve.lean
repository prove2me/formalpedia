-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_ve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:56.220802+00:00
-- url     : https://prove2.me/submissions/b92e636c-4ac9-47f8-8107-4e0bf463146f

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
    Pat k r l (Matrix.single (posL k r l.succ j) (esI k r l) 1) := by
  have h := posL_val (k := k) l j
  have hl := l.isLt
  apply pat_single
  right
  exact ⟨rfl, by omega, by omega⟩
end Formalism.FourierDecayAlt.Q.QRR
