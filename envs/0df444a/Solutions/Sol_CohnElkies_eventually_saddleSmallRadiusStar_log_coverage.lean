-- Prove2me | solution 1 for CohnElkies.eventually_saddleSmallRadiusStar_log_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/95f05e14-9449-44e1-8f22-b02ad51c3f03

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleLogRadius_covers_Ici
import Theorems.Thm_CohnElkies_eventually_saddleSmallRadiusStarOrdinate_gt_neg_one

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSmallRadiusStar ε d ≤ r →
            ∃ u : ℝ,
              saddleSmallRadiusStarOrdinate ε d ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by
  filter_upwards
    [eventually_saddleLogRadius_covers_Ici]
    with ε hcoverage
  filter_upwards
    [eventually_saddleSmallRadiusStarOrdinate_gt_neg_one ε,
      eventually_gt_atTop (0 : ℕ)]
    with d hstar hd
  intro r hr
  apply hcoverage d hd
    (saddleSmallRadiusStarOrdinate ε d) hstar r
  exact hr
end CohnElkies
