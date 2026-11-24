-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coe_untopD_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:46.719462+00:00
-- url     : https://prove2.me/submissions/3164e5ff-a5f3-488d-bffb-a8883e195666

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (x : WithTop ℤ) : ((x.untopD 0 : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n => exact le_rfl
end Formalism.MainNotions.PlaneGram
