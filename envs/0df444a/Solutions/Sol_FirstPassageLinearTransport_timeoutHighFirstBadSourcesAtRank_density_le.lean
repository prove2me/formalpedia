-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:03.141002+00:00
-- url     : https://prove2.me/submissions/9bd88028-c986-4516-b55b-cf4157a7a19c

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Theorems.Thm_FirstPassageLinearTransport_timeoutHighFirstBadSourcesAtRank_card_le
import Theorems.Thm_FirstPassageLinearTransport_rank_transport_multiplier_le


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
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hTarget :
      ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
        (2 : ℝ) ^ q ≤ d) :
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcardQ := timeoutHighFirstBadSourcesAtRank_card_le
    (S := S) hrStar hStarHi hStarLo hM hqM hsmall
  have hcard :
      ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) ≤
        ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) := by
    exact_mod_cast hcardQ
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hmult := rank_transport_multiplier_le hrR q
  have hTimes0 : 0 ≤
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) := by positivity
  calc
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ)) /
            (2 : ℝ) ^ M := div_le_div_of_nonneg_right hcard hpowM.le
    _ = ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
        (1 + 3 * (((q + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
        (((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
          (2 : ℝ) ^ q) := by field_simp
    _ ≤ ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
        ((1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
        (((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
          (2 : ℝ) ^ q) := by
      have := hmult
      gcongr
    _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
      have hH0 : 0 ≤ H := hTimes0.trans hTimes
      have hT0 : 0 ≤
          ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
            (2 : ℝ) ^ q := by positivity
      calc
        _ ≤ H * ((1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
            (((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
              (2 : ℝ) ^ q) := by gcongr
        _ ≤ H * ((1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) * d := by
          gcongr
        _ = _ := by ring
end FirstPassageLinearTransport
