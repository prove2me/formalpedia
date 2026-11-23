-- Prove2me | solution 1 for Formalism.L2.LamCM.CMNumbersLink_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:51.137417+00:00
-- url     : https://prove2.me/submissions/97b802ba-0fdc-4d58-9c18-1a8e68eb8c54

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois

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
theorem _root_.solution (hH : HadamardIdeals) (hD : DetGood) : CMNumbersLink := by
  unfold CMNumbersLink
  intro K _ _ g Lie ℓ u de La logOm h
  unfold CMNumbers at h
  unfold CMNumbers0
  obtain ⟨hL, hℓ, hde, hu, hmem, hLa, hsq, hnd, hdd⟩ := h
  exact ⟨(hD K g Lie hL).2, hℓ, hde, hLa, hH K g Lie ℓ u La hL hℓ hu hmem (by linarith) hsq, hnd, hdd⟩
end Formalism.L2.LamCM
