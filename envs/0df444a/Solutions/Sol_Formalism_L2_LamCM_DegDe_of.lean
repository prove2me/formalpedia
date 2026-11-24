-- Prove2me | solution 1 for Formalism.L2.LamCM.DegDe_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:25.809275+00:00
-- url     : https://prove2.me/submissions/a2cb73ef-07a3-4729-8813-2730fff75241

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_degree_delta_base
import Theorems.Thm_Formalism_L2_LamCM_CMNumbersLink_of

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
namespace Formalism.L2.LamCM
theorem _root_.solution (hH : HadamardIdeals) (hD : DetGood) : DegDe := by
  unfold DegDe
  intro K _ _ g Lie ℓ u de La logOm h
  exact degree_delta_base K g _ ℓ de La logOm (CMNumbersLink_of hH hD K g Lie ℓ u de La logOm h)
end Formalism.L2.LamCM
