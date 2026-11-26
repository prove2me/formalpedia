-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:38.094797+00:00
-- url     : https://prove2.me/submissions/bc09e5e8-3f2c-4f8c-8a7b-001d1949ab8b

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Theorems.Thm_FirstPassageLinearTransport_rank_transport_multiplier_le
import Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_card_le


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
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
      ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget :
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤ d) :
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) * d := by
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcardQ := timeoutFirstBadSourcesAtRank_card_le
    (S := S) hrStar hStarHi hStarLo hM hp hnextPos hnextLt hpM hsmall
  have hcard :
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) ≤
        ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
          (1 + 3 * (((p + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ p *
          ((timeoutLandingBad K₀ L p).card : ℝ) := by
    exact_mod_cast hcardQ
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hmult := rank_transport_multiplier_le hrR p
  have hTimes0 : 0 ≤
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) := by positivity
  calc
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
          (1 + 3 * (((p + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ p *
          ((timeoutLandingBad K₀ L p).card : ℝ)) /
            (2 : ℝ) ^ M := div_le_div_of_nonneg_right hcard hpowM.le
    _ = ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
        (1 + 3 * (((p + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
        (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) := by
      field_simp
    _ ≤ ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
        ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) *
        (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) := by
      have := hmult
      gcongr
    _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) * d := by
      have hH0 : 0 ≤ H := hTimes0.trans hTimes
      have hC : 0 ≤ 1 + 6 / (rStar : ℝ) := by positivity
      have hp0 : 0 ≤ ((p + 1 : ℕ) : ℝ) := by positivity
      have hT0 : 0 ≤
          ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p := by positivity
      calc
        ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
            ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) *
            (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) ≤
          H * ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) *
            (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) := by
          gcongr
        _ ≤ H * ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) * d := by
          gcongr
        _ = _ := by ring
end FirstPassageLinearTransport
