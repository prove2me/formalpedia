-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:38.388803+00:00
-- url     : https://prove2.me/submissions/c0275635-b798-46b9-9eaa-9c53763bef46

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_subset_transport
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_atTimes_uniform


set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (hpM : p < M)
    (hsmall : ((((p + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3) :
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℚ) ≤
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℚ) *
        (1 + 3 * (((p + 2 : ℕ) : ℚ) / rStar)) *
          (2 : ℚ) ^ M / ((2 ^ p : ℕ) : ℚ) *
        ((timeoutLandingBad K₀ L p).card : ℚ) := by
  have hsubset := timeoutFirstBadSourcesAtRank_subset_transport
    (S := S) hrStar hStarHi hStarLo hM hp hnextPos hnextLt
  have hcardNat := Finset.card_le_card hsubset
  have hcardQ :
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℚ) ≤
        ((lossFilteredTransportedSourcesAtTimes M (2 ^ p)
          (timeoutFeasibleTimes P K₀ L M S p)
          (timeoutLandingBad K₀ L p)
          (((p + 2 : ℕ) : ℚ) / rStar)).card : ℚ) := by
    exact_mod_cast hcardNat
  exact hcardQ.trans
    (lossFiltered_arbitraryTarget_transport_atTimes_uniform
      (timeoutFeasibleTimes P K₀ L M S p)
      (timeoutLandingBad K₀ L p)
      (by positivity)
      (div_nonneg (by positivity) hrStar.le) hsmall
      (Nat.pow_lt_pow_right (by omega) hpM))
end FirstPassageLinearTransport
