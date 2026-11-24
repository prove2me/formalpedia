-- Prove2me | solution 1 for Formalism.L2.LamCM.eq_bcI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:06.589854+00:00
-- url     : https://prove2.me/submissions/b12e2a72-9085-4998-9078-ae08721683ed

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_coe_bcI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution {L : MLine K} {L1 : MLine K1} (h : IsBaseChangeLine L L1) : L1.I = bcI L.I := by
  unfold IsBaseChangeLine at h
  exact FractionalIdeal.coeToSubmodule_injective (h.1.trans (coe_bcI L.I).symm)
end Formalism.L2.LamCM
