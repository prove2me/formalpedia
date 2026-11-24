-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.val_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:20.711122+00:00
-- url     : https://prove2.me/submissions/b62117f6-b8c1-45e1-a572-5187bea081db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_row
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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) (j : Fin (mdim k r l.succ)) :
    ell k r z (Matrix.single (eI k r l) (posL k r l.succ j) 1) +
      star (ell k r z (dag k r (Matrix.single (eI k r l) (posL k r l.succ j) 1))) = xv k r z l.succ j := by
  rw [dag_single, tau_eI, ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), star_zero, add_zero,
    ell_single_row]
  unfold xv fvec
  by_cases h : l.val + 1 < r
  · rw [dif_pos h, dif_pos (show l.succ.val < r from h)]
    simp only [bvec, Pi.single_apply]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ l.succ.val < r from h), one_mul]
end Formalism.FourierDecayAlt.Q.QRR
