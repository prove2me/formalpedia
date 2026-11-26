-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.source_mem_dyadicShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:17:59.354284+00:00
-- url     : https://prove2.me/submissions/2ecf1f9e-bf45-45d0-8957-9b4110983039

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
    n ∈ dyadicShell M := by
  induction hrun with
  | first hSM hM0 hnShell hnGood => exact hnShell
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih => exact ih
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap ih => exact ih
end TimeoutRecertificationRun
end FirstPassageLinearTransport
