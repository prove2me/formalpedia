-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.landingBand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:42:54.383536+00:00
-- url     : https://prove2.me/submissions/6cb69df3-68c4-41d4-a193-7172de43dab4

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_band


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    2 ^ q < 2 * orbit elapsed n ∧ orbit elapsed n ≤ 2 ^ q :=
  firstPassage_band hrun.elapsed_pos hrun.directFirstPassage
end TimeoutRecertificationRun
end FirstPassageLinearTransport
