-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.elapsed_le_horizon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:40.577341+00:00
-- url     : https://prove2.me/submissions/fa49f120-39ff-4f2c-94a2-fde9e7328b3e

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_toRankTrace
import Theorems.Thm_FirstPassageLinearTransport_TwoRegimeRankTrace_elapsed_le
import Theorems.Thm_FirstPassageLinearTransport_twoRegimeHorizon_lower


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace ShrinkingRecertificationRun
theorem _root_.solution
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    elapsed ≤ twoRegimeHorizon P.rHi P.rLo S M := by
  have hreal := hrun.toRankTrace.elapsed_le
    P.pHi.r_pos.le P.pHi.r_lt_one P.pLo.r_lt_one
  have hceil := twoRegimeHorizon_lower P.rHi P.rLo S M
  exact_mod_cast hreal.trans hceil
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
