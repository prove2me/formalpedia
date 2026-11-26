-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.elapsed_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:30.005241+00:00
-- url     : https://prove2.me/submissions/f7e83f3f-7a08-4288-ab2d-3408d00821f6

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_stageLength_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace ShrinkingRecertificationRun
theorem _root_.solution
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    0 < elapsed := by
  cases hrun with
  | first hSM hM0 hnShell hnGood =>
      exact stageLength_pos (shrinkingHighSetup P M M) hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hsourceShell hsourceGood hgap =>
      have hstage := stageLength_pos (shrinkingHighSetup P M _) hm0
        hsourceShell hsourceGood
      omega
  | nextLo hrun hmS hm0 hsourceShell hsourceGood hgap =>
      have hstage := stageLength_pos P.pLo hm0 hsourceShell hsourceGood
      omega
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
