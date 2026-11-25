-- Prove2me | solution 1 for CompanionTheory.RgFd.momW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:18.065924+00:00
-- url     : https://prove2.me/submissions/53c68434-2afd-49bf-aaa5-70a637bfb5a3

import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomB
import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomentRecursion_MomStep
import Theorems.Thm_CompanionTheory_RgFd_momA
import Theorems.Thm_CompanionTheory_RgFd_momB
import Theorems.Thm_CompanionTheory_RgFd_momW_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.RgFd
namespace CompanionTheory.RgFd
theorem _root_.solution : MomW := momW_of momA momB
end CompanionTheory.RgFd
