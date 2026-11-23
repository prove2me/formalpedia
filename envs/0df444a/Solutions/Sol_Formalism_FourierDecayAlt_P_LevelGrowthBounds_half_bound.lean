-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.half_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:17.918152+00:00
-- url     : https://prove2.me/submissions/5856a0fd-9cf8-470a-9164-54c5da707030

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LevelGrowthBounds
open Finset Real
namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds
theorem _root_.solution (r : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (hr : (r:ℝ) * (12 * u) ≤ 1) :
    ((r:ℝ) + 1) * (3 * u) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp; linarith
  · have h1 : (1:ℝ) ≤ r := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h1 hu0]
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
