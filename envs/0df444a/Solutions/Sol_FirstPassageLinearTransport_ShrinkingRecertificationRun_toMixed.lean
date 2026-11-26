-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.toMixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:17:23.506134+00:00
-- url     : https://prove2.me/submissions/7cbed50b-2e35-4b90-8ea7-717f2fed5aed

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace ShrinkingRecertificationRun
theorem _root_.solution
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    MixedRecertificationRun P.rStar n elapsed q := by
  rw [P.rStar_eq]
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      exact MixedRecertificationRun.first (shrinkingHighSetup P M M)
        (min_le_left _ _) hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      exact MixedRecertificationRun.next ih (shrinkingHighSetup P M _)
        (min_le_left _ _) hm0 hsourceShell hsourceGood hgap
  | nextLo hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      exact MixedRecertificationRun.next ih P.pLo
        (min_le_right _ _) hm0 hsourceShell hsourceGood hgap
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
