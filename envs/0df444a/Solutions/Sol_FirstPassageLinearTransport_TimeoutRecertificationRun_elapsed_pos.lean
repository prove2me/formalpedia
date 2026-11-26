-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.elapsed_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:41:36.780337+00:00
-- url     : https://prove2.me/submissions/24e6322b-da90-4b11-b7d0-20b60926f01b

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_stageLength_pos


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    0 < elapsed := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      exact stageLength_pos (timeoutHighSetup P M M) hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      have hstage := stageLength_pos (timeoutHighSetup P M _) hm0
        hsourceShell hsourceGood
      omega
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap ih =>
      exact Nat.lt_add_right _ ih
end TimeoutRecertificationRun
end FirstPassageLinearTransport
