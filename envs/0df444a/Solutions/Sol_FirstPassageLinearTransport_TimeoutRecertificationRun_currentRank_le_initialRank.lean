-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_le_initialRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:36.269653+00:00
-- url     : https://prove2.me/submissions/3b03a5f2-d230-480b-a8e4-08b7ddaef83d

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    q ≤ rationalTargetRank P.rHi M := by
  induction hrun with
  | first hSM hM0 hnShell hnGood => exact le_rfl
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      exact hgap.le.trans ih
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos
      hqparent hgap ih =>
      exact hgap.le.trans ih
end TimeoutRecertificationRun
end FirstPassageLinearTransport
