-- Prove2me | solution 1 for FreyCurve.isPeuRamifieeAt_odd_of_integralForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3f3baf60-2d15-5dad-8c80-f435462442d2

import Mathlib
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_p_dvd_padicValRat_freyCurve_discr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm

set_option autoImplicit false

open FreyPackage

theorem solution (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) : P.freyCurve.IsPeuRamifieeAt P.p q :=
  FreyPackage.p_dvd_padicValRat_freyCurve_discr P Fact.out hq2

end S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm
end P2MW
export P2MW.S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm (solution)
