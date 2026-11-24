-- Prove2me | solution 1 for Formalism.L2.LamCM.DegNN_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:42:52.301422+00:00
-- url     : https://prove2.me/submissions/996597f5-fe4e-4422-b9d0-997546060c38

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_degree_norm_base
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
theorem _root_.solution (hH : HadamardIdeals) (hD : DetGood) : DegNN := by
  unfold DegNN
  intro K _ _ g Lie ℓ u de La logOm V _ c μ n h
  exact degree_norm_base K g _ ℓ de La logOm V c μ n (CMNumbersLink_of hH hD K g Lie ℓ u de La logOm h)
end Formalism.L2.LamCM
