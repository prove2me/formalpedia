-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.ruleRight_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:50.861387+00:00
-- url     : https://prove2.me/submissions/b12d1d59-294f-4ee2-a11e-af5054ada6a8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_val_ev
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_val_ve
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_val_ees
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_ev
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_ve
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_ees
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_lam


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
theorem _root_.solution : RuleRight := by
  intro E _ _ k r z' l D f hz _ _ hR g hg
  refine ⟨fun j => ?_, fun j => ?_, ?_⟩
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [lam z' hz l D f hR g hg _ (pat_ev l j), val_ev z' hz l j]
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [lam z' hz l D f hR g hg _ (pat_ve l j), val_ve z' hz l j]
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [lam z' hz l D f hR g hg _ (pat_ees l), val_ees z' hz l, zero_smul]
end Formalism.FourierDecayAlt.Q.QRR
