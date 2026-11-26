-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:40.078734+00:00
-- url     : https://prove2.me/submissions/fe8b32b1-4430-4ed0-a243-300f3e2b1413

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Theorems.Thm_FirstPassageLinearTransport_shrinkingFirstBadSourcesAtRank_subset_transport
import Theorems.Thm_FirstPassageLinearTransport_lossFiltered_arbitraryTarget_transport_atTimes_uniform


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / P.rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℚ) ≤
      ((shrinkingFeasibleTimes P M S q).card : ℚ) *
        (1 + 3 * (((q + 2 : ℕ) : ℚ) / P.rStar)) *
          (2 : ℚ) ^ M / ((2 ^ q : ℕ) : ℚ) *
        ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℚ) := by
  have hsubset := shrinkingFirstBadSourcesAtRank_subset_transport P
    (M := M) (S := S) (q := q)
  have hcardNat := Finset.card_le_card hsubset
  have hcardQ :
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℚ) ≤
        ((lossFilteredTransportedSourcesAtTimes M (2 ^ q)
          (shrinkingFeasibleTimes P M S q)
          (landingBad q (shrinkingTargetTolerance P M S q))
          (((q + 2 : ℕ) : ℚ) / P.rStar)).card : ℚ) := by
    exact_mod_cast hcardNat
  exact hcardQ.trans
    (lossFiltered_arbitraryTarget_transport_atTimes_uniform
      (shrinkingFeasibleTimes P M S q)
      (landingBad q (shrinkingTargetTolerance P M S q))
      (by positivity)
      (div_nonneg (by positivity) P.rStar_pos.le) hsmall
      (Nat.pow_lt_pow_right (by omega) hqM))
end FirstPassageLinearTransport
