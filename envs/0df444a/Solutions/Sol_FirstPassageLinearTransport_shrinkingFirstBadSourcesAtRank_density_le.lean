-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:40.488345+00:00
-- url     : https://prove2.me/submissions/489a4d07-6864-45aa-9783-beb117ffc508

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Theorems.Thm_FirstPassageLinearTransport_rank_transport_multiplier_le
import Theorems.Thm_FirstPassageLinearTransport_shrinkingFirstBadSourcesAtRank_card_le


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / P.rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H)
    (hTarget :
      ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
        (2 : ℝ) ^ q ≤ d) :
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
  have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
  have hcardQ := shrinkingFirstBadSourcesAtRank_card_le P
    (M := M) (S := S) (q := q) hqM hsmall
  have hcard :
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) ≤
        ((shrinkingFeasibleTimes P M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (P.rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) := by
    exact_mod_cast hcardQ
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hpowq : 0 < (2 : ℝ) ^ q := by positivity
  have hmult := rank_transport_multiplier_le hrR q
  have hTimes0 : 0 ≤
      ((shrinkingFeasibleTimes P M S q).card : ℝ) := by positivity
  have hTarget0 : 0 ≤
      ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
        (2 : ℝ) ^ q := by positivity
  calc
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((shrinkingFeasibleTimes P M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (P.rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ)) /
            (2 : ℝ) ^ M := div_le_div_of_nonneg_right hcard hpowM.le
    _ = ((shrinkingFeasibleTimes P M S q).card : ℝ) *
        (1 + 3 * (((q + 2 : ℕ) : ℝ) / (P.rStar : ℝ))) *
        (((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
          (2 : ℝ) ^ q) := by field_simp
    _ ≤ ((shrinkingFeasibleTimes P M S q).card : ℝ) *
        ((1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
        (((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
          (2 : ℝ) ^ q) := by
      gcongr
    _ ≤ H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
      have hC : 0 ≤ 1 + 6 / (P.rStar : ℝ) := by positivity
      have hq0 : 0 ≤ ((q + 1 : ℕ) : ℝ) := by positivity
      have hH0 : 0 ≤ H := hTimes0.trans hTimes
      calc
        _ ≤ H * ((1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
            (((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
              (2 : ℝ) ^ q) := by
          gcongr
        _ ≤ H * ((1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) * d := by
          gcongr
        _ = _ := by ring
end FirstPassageLinearTransport
