-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.scaledReverseLoss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:39.302898+00:00
-- url     : https://prove2.me/submissions/eab6cedc-7127-4c24-9de5-2bc8bd51ff43

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_scaledReverseLoss_le
import Theorems.Thm_FirstPassageLinearTransport_MixedRecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S n elapsed q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    scaledReverseLoss (2 ^ q) n elapsed ≤ ((q + 2 : ℕ) : ℚ) / rStar :=
  (hrun.toCertifiedRankChain hrStar hStarHi hStarLo).scaledReverseLoss_le hrStar
end TimeoutRecertificationRun
end FirstPassageLinearTransport
