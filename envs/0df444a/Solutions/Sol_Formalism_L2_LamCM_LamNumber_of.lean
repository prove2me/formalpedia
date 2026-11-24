-- Prove2me | solution 1 for Formalism.L2.LamCM.LamNumber_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:58:54.08185+00:00
-- url     : https://prove2.me/submissions/815e16cf-0574-415c-9463-b9911e973e88

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_CMNumbersLink_of
import Theorems.Thm_Formalism_L2_LamCM_lambda_number_base

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
theorem _root_.solution (hH : HadamardIdeals) (hD : DetGood) : LamNumber := by
  unfold LamNumber
  intro K _ _ g Lie ℓ u de La logOm V _ c G μ n S Rr h
  exact lambda_number_base K g _ ℓ de La logOm V c G μ n S Rr (CMNumbersLink_of hH hD K g Lie ℓ u de La logOm h)
end Formalism.L2.LamCM
