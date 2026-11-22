-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.Pp_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:31.86152+00:00
-- url     : https://prove2.me/submissions/60bdf448-cbf8-4854-8069-713584e37149

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
theorem _root_.solution (e : ℕ → ℝ) (i : ℕ) : Pp e (i+1) = Pp e i * √(1 + e (i+1)) := by
  unfold Pp
  rw [Finset.prod_Icc_succ_top (by omega)]
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
