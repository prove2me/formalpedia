-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.one_le_sqrt_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:47.077476+00:00
-- url     : https://prove2.me/submissions/a951687f-e767-4e9d-9c42-5a122e2f23bd

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
theorem _root_.solution {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (l : ℕ) : (1:ℝ) ≤ √(1 + e l) := by
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + e l by linarith [he l])
  rwa [Real.sqrt_one] at this
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
