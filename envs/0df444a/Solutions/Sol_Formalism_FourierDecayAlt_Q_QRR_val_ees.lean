-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.val_ees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:19.686794+00:00
-- url     : https://prove2.me/submissions/2f412b67-0be7-4dff-ae5b-ff422b047e44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_single
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_eI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_esI_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_esI_ge

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) :
    ell k r z (Matrix.single (eI k r l) (esI k r l) 1) +
      star (ell k r z (dag k r (Matrix.single (eI k r l) (esI k r l) 1))) = 0 := by
  rw [ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), zero_add, dag_single, tau_eI,
    ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), star_zero]
end Formalism.FourierDecayAlt.Q.QRR
