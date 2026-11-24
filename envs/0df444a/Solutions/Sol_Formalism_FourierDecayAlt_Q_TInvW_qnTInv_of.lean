-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:51.699798+00:00
-- url     : https://prove2.me/submissions/3f08796b-9dba-428d-a6a7-e5d3c0235398

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_QnTInvOf
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tInvariant_of_contractions
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_congruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_group_mul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_restriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH) :
    TInvariant :=
  tInvariant_of_contractions hCC hP hG hL transfer_invariance_smooth transfer_invariance_group_mul transfer_invariance_vector transfer_invariance_congruence
    transfer_invariance_right transfer_invariance_restriction
end Formalism.FourierDecayAlt.Q.TInvW
