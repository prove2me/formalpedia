-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.directFirstPassage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:51.99066+00:00
-- url     : https://prove2.me/submissions/2acc9f24-9968-4955-a572-1ae61b0ab482

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_toMixed
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_MixedRecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace ShrinkingRecertificationRun
theorem _root_.solution
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    IsFirstPassage (2 ^ q) n elapsed :=
  (hrun.toMixed.toCertifiedRankChain P.rStar_pos).directFirstPassage
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
