-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.total_le_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:35.760009+00:00
-- url     : https://prove2.me/submissions/9122c5dd-a800-4a84-b725-9e4105bb3b27

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution (d D T c RR γ κ P1 P2 P3 P4 PP : ℝ)
    (hd : 0 ≤ d) (hT : 0 < T) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (h1 : P1 * D ^ 2 ≤ PP ^ 2 * D ^ 3) (h2 : P2 ≤ PP ^ 3) (h3 : P3 ≤ PP ^ 2) (h4 : P4 ≤ PP ^ 2) :
    d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ) ≤
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by
  have a1 : P1 * D ^ 2 * (κ / T) ≤ PP ^ 2 * D ^ 3 * (κ / T) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have a2 : P2 * T ≤ PP ^ 3 * T := mul_le_mul_of_nonneg_right h2 hT.le
  have a3 : P3 * (T * c) ≤ PP ^ 2 * (T * c) := mul_le_mul_of_nonneg_right h3 (by positivity)
  have a4 : P4 * ((1 / T + RR ^ 2 * c) * κ / γ) ≤ PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hsum : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ ≤
      PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T := by
    have e : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ =
        P1 * D ^ 2 * (κ / T) + P2 * T + P3 * (T * c) + P4 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    have e' : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T =
        PP ^ 2 * D ^ 3 * (κ / T) + PP ^ 3 * T + PP ^ 2 * (T * c) + PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    rw [e, e']
    linarith
  calc d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ)
      ≤ d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T) :=
        mul_le_mul_of_nonneg_left hsum hd
    _ = d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by ring
end Formalism.MainNotions.Gaps.T0
