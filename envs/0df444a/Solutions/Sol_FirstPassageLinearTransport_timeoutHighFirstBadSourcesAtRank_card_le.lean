-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:32.778796+00:00
-- url     : https://prove2.me/submissions/08693ee3-7bbb-47e3-983d-d6eedf2c8656

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Theorems.Thm_FirstPassageLinearTransport_timeoutHighFirstBadSourcesAtRank_subset_transport
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_atTimes_uniform


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℚ) ≤
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℚ) *
        (1 + 3 * (((q + 2 : ℕ) : ℚ) / rStar)) *
          (2 : ℚ) ^ M / ((2 ^ q : ℕ) : ℚ) *
        ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℚ) := by
  have hsubset := timeoutHighFirstBadSourcesAtRank_subset_transport
    (S := S) (q := q) hrStar hStarHi hStarLo hM
  have hcardNat := Finset.card_le_card hsubset
  have hcardQ :
      ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℚ) ≤
        ((lossFilteredTransportedSourcesAtTimes M (2 ^ q)
          (timeoutFeasibleTimes P K₀ L M S q)
          (landingBad q (timeoutHighTargetTolerance P M q))
          (((q + 2 : ℕ) : ℚ) / rStar)).card : ℚ) := by
    exact_mod_cast hcardNat
  exact hcardQ.trans
    (lossFiltered_arbitraryTarget_transport_atTimes_uniform
      (timeoutFeasibleTimes P K₀ L M S q)
      (landingBad q (timeoutHighTargetTolerance P M q))
      (by positivity)
      (div_nonneg (by positivity) hrStar.le) hsmall
      (Nat.pow_lt_pow_right (by omega) hqM))
end FirstPassageLinearTransport
